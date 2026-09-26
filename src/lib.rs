#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![warn(missing_docs, missing_debug_implementations)]

//! This crate provides PolyXOR128, a 128-bit [universal hash function](https://en.wikipedia.org/wiki/Universal_hashing)
//! designed for fast file/data stream integrity checks with cryptographic strength.
//!
//! See the [readme](https://github.com/orlp/polyxor) for more details.
//!
//! ## Usage
//!
//! You should construct a [`PolyXor128`] instance with a random key, use its
//! [`hasher`](PolyXor128::hasher) method to get a hasher, and then one of its
//! finalize methods to extract the hash or message authentication tag:
//!  - [`finalize_raw`](PolyXor128Hasher::finalize_raw)
//!  - [`finalize_avalanche`](PolyXor128Hasher::finalize_avalanche) / [`finalize_avalanche_with_tweak`](PolyXor128Hasher::finalize_avalanche_with_tweak)
//!  - [`finalize_mac`](PolyXor128Hasher::finalize_mac)
//!
//! For example:
//!
//! ```rust
//! use polyxor::PolyXor128;
//!
//! // Constructing a hash instance with a random key with `getrandom`.
//! let mut key = [0u8; 16];
//! getrandom::fill(&mut key).unwrap();
//! let polyxor = PolyXor128::from_key(u128::from_le_bytes(key));
//!
//! // Hashing some data.
//! let mut hasher = polyxor.hasher();
//! hasher.update(b"hello world");
//! let hash = hasher.finalize_avalanche();
//! ```
//!
//! ## Features
//!
//! This crate has the following features:
//!
//!  - `aes`, enables seeding from key and message authentication code support,
//!  - `runtime_detection`, enables automatic detection of CPU features at runtime to dispatch to
//!    the best available hardware-accelerated implementation,
//!  - `zeroize`, adds zeroing support of sensitive key material, and
//!  - `std`, this feature adds features gated behind stdlib support.
//!
//! All besides `zeroize` are enabled by default.

use core::cell::Cell;
use core::mem::MaybeUninit;

#[cfg(feature = "aes")]
use aes::{
    Aes128Enc,
    cipher::{Array, BlockCipherEncrypt, KeyInit},
};

mod dispatch;

// Without runtime_detection there is no runtime feature detection, so only the backend
// selected at compile time is used.
#[cfg(target_arch = "aarch64")]
#[cfg_attr(not(feature = "runtime_detection"), allow(dead_code))]
mod neon;
#[cfg_attr(not(feature = "runtime_detection"), allow(dead_code))]
mod reference;
#[cfg(target_arch = "x86_64")]
#[cfg_attr(not(feature = "runtime_detection"), allow(dead_code))]
mod x86_64;

use dispatch::{gf128mul, hash_blocks};

const INNER_BLOCK_SIZE: usize = 128; // Must be 128, fundamental to algorithm.
const OUTER_BLOCK_SIZE: usize = 4096; // Must be multiple of INNER_BLOCK_SIZE.

#[derive(Clone)]
#[repr(align(64))]
pub(crate) struct BlockKey([u8; OUTER_BLOCK_SIZE]);

/// An instance of the PolyXOR128 universal hash.
#[derive(Clone)]
pub struct PolyXor128 {
    block_key: BlockKey,
    poly_z: u128,
    poly_u: u128,
    poly_y: u128,
    avalanche_mul: u128,
    #[cfg(feature = "aes")]
    aes_key: Option<Aes128Enc>,
}

impl core::fmt::Debug for PolyXor128 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("PolyXor128 { .. }")
    }
}

impl PolyXor128 {
    /// The number of bytes of entropy [`from_entropy`](Self::from_entropy) needs.
    #[must_use]
    pub const fn entropy_needed() -> usize {
        OUTER_BLOCK_SIZE + 64
    }

    /// Creates a PolyXOR128 instance from a 128-bit key.
    ///
    /// All hash parameters are derived from the key using AES-128, and the
    /// key is also used for [`finalize_mac`](PolyXor128Hasher::finalize_mac).
    #[cfg(feature = "aes")]
    #[must_use]
    pub fn from_key(key: u128) -> Self {
        let mut entropy = [0u8; PolyXor128::entropy_needed()];
        for (i, arr) in entropy.as_chunks_mut::<16>().0.iter_mut().enumerate() {
            *arr = ((1u128 << 127) | i as u128).to_le_bytes();
        }

        let aes_key = Aes128Enc::new(&key.to_le_bytes().into());
        aes_key.encrypt_blocks(Array::cast_slice_from_core_mut(entropy.as_chunks_mut().0));

        let mut slf = Self::from_entropy(&entropy);
        slf.aes_key = Some(aes_key);
        slf
    }

    /// Creates a PolyXOR128 instance from pre-existing entropy.
    /// These must be uniformly random bytes.
    ///
    /// # Panics
    ///
    /// Panics if `bytes.len() < Self::entropy_needed()`.
    #[must_use]
    pub fn from_entropy(bytes: &[u8]) -> Self {
        assert!(bytes.len() >= Self::entropy_needed());

        let poly_z = u128::from_le_bytes(*bytes[0..16].as_array().unwrap());
        let poly_u = u128::from_le_bytes(*bytes[16..32].as_array().unwrap());
        let poly_y = u128::from_le_bytes(*bytes[32..48].as_array().unwrap());
        let avalanche_mul = u128::from_le_bytes(*bytes[48..64].as_array().unwrap());
        let block_key = BlockKey(*bytes[64..64 + OUTER_BLOCK_SIZE].as_array().unwrap());

        Self {
            block_key,
            poly_z,
            poly_u,
            poly_y,
            avalanche_mul: avalanche_mul.max(1), // Avoid total collapse for zero mul.
            #[cfg(feature = "aes")]
            aes_key: None,
        }
    }

    /// Starts hashing a new message with this instance.
    #[must_use]
    pub fn hasher(&self) -> PolyXor128Hasher<'_> {
        PolyXor128Hasher {
            params: self,
            sponge: [const { Cell::new(MaybeUninit::uninit()) }; OUTER_BLOCK_SIZE],
            poly_accum: self.poly_z,
            count: 0,
        }
    }
}

#[cfg(feature = "zeroize")]
impl Drop for PolyXor128 {
    fn drop(&mut self) {
        use zeroize::Zeroize;

        // The AES key schedule zeroizes itself on drop since we
        // propagate aes?/zeroize.
        self.block_key.0.zeroize();
        self.poly_z.zeroize();
        self.poly_u.zeroize();
        self.poly_y.zeroize();
        self.avalanche_mul.zeroize();
    }
}

#[cfg(feature = "zeroize")]
impl zeroize::ZeroizeOnDrop for PolyXor128 {}

/// An in-progress hash state.
#[derive(Clone)]
pub struct PolyXor128Hasher<'a> {
    params: &'a PolyXor128,
    // We need Cell for interior mutability in finalize_raw(&self), to pad to INNER_BLOCK_SIZE.
    sponge: [Cell<MaybeUninit<u8>>; OUTER_BLOCK_SIZE],
    count: u64,
    poly_accum: u128,
}

impl<'a> core::fmt::Debug for PolyXor128Hasher<'a> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("PolyXor128Hasher { .. }")
    }
}

#[cfg(feature = "zeroize")]
impl<'a> Drop for PolyXor128Hasher<'a> {
    fn drop(&mut self) {
        use zeroize::Zeroize;

        self.zeroize_sponge();
        self.poly_accum.zeroize();
    }
}

#[cfg(feature = "zeroize")]
impl<'a> zeroize::ZeroizeOnDrop for PolyXor128Hasher<'a> {}

#[cfg(feature = "zeroize")]
impl<'a> PolyXor128Hasher<'a> {
    /// Wipes every sponge byte that may have been written.
    fn zeroize_sponge(&mut self) {
        use zeroize::Zeroize;

        // SAFETY: Cell<T> is repr(transparent) and we have exclusive access.
        let written = self.count.min(OUTER_BLOCK_SIZE as u64) as usize;
        let sponge = unsafe {
            core::slice::from_raw_parts_mut(
                self.sponge.as_mut_ptr().cast::<MaybeUninit<u8>>(),
                written,
            )
        };
        sponge.zeroize();
    }
}

impl<'a> PolyXor128Hasher<'a> {
    /// Add input bytes to the hash state.
    pub fn update(&mut self, mut bytes: &[u8]) {
        let sponge_len = self.count as usize % OUTER_BLOCK_SIZE;
        if sponge_len != 0 {
            let max_absorb = bytes.len().min(OUTER_BLOCK_SIZE - sponge_len);
            unsafe {
                core::ptr::copy_nonoverlapping(
                    bytes.as_ptr(),
                    self.sponge.as_mut_ptr().add(sponge_len).cast(),
                    max_absorb,
                );
                self.count += max_absorb as u64;
            }
            if sponge_len + max_absorb < OUTER_BLOCK_SIZE {
                return;
            }

            hash_blocks(
                unsafe { self.sponge.align_to().1 },
                self.params,
                &mut self.poly_accum,
            );
            bytes = &bytes[max_absorb..];
        }

        let whole_chunks = bytes.len() / OUTER_BLOCK_SIZE;
        if whole_chunks > 0 {
            let process_size = whole_chunks * OUTER_BLOCK_SIZE;
            hash_blocks(&bytes[..process_size], self.params, &mut self.poly_accum);
            self.count += process_size as u64;
            bytes = &bytes[process_size..];
        }

        unsafe {
            core::ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                self.sponge.as_mut_ptr().cast(),
                bytes.len(),
            );
            self.count += bytes.len() as u64;
        }
    }

    /// Directly output the almost-XOR-universal hash without any blinding or
    /// avalanching.
    ///
    /// Note that the universality guarantees low collision chance on any subset
    /// of bits, but does not guarantee other properties such as the avalanche
    /// effect. See [`finalize_avalanche`](Self::finalize_avalanche) for a
    /// 128-bit output that more closely matches a random oracle's properties.
    ///
    /// <div class="warning">
    ///
    /// All security is lost if a malicious party sees (part of) the hash
    /// output. For publicly transferable message authentication codes, see
    /// [`finalize_mac`](Self::finalize_mac).
    ///
    /// </div>
    #[must_use]
    pub fn finalize_raw(&self) -> u128 {
        let mut poly_accum = self.poly_accum;
        let sponge_len = self.count as usize % OUTER_BLOCK_SIZE;
        if sponge_len != 0 {
            let process_len = sponge_len.next_multiple_of(INNER_BLOCK_SIZE);
            unsafe {
                core::ptr::write_bytes(
                    self.sponge.as_ptr().add(sponge_len).cast_mut(),
                    0,
                    process_len - sponge_len,
                );
                hash_blocks(
                    self.sponge[..process_len].align_to().1,
                    self.params,
                    &mut poly_accum,
                );
            }
        }

        gf128mul(
            poly_accum ^ self.params.poly_u,
            self.count as u128 ^ self.params.poly_y,
        )
    }

    /// Output the almost-XOR-universal hash with minimal avalanching to make it
    /// behave more like a random oracle.
    ///
    /// <div class="warning">
    ///
    /// All security is lost if a malicious party sees (part of) the hash
    /// output. For publicly transferable message authentication codes, see
    /// [`finalize_mac`](Self::finalize_mac).
    ///
    /// </div>
    #[must_use]
    pub fn finalize_avalanche(&self) -> u128 {
        self.finalize_avalanche_with_tweak(0)
    }

    /// Output the almost-XOR-universal hash with minimal avalanching to make it
    /// behave more like a random oracle.
    ///
    /// The 64-bit `tweak` is mixed in before avalanching, so different tweaks
    /// give unrelated-looking outputs for the same message. The tweak does not
    /// affect collisions: if two messages collide in
    /// [`finalize_raw`](Self::finalize_raw), they collide for every tweak.
    ///
    /// <div class="warning">
    ///
    /// All security is lost if a malicious party sees (part of) the hash
    /// output. For publicly transferable message authentication codes, see
    /// [`finalize_mac`](Self::finalize_mac).
    ///
    /// </div>
    #[must_use]
    pub fn finalize_avalanche_with_tweak(&self, tweak: u64) -> u128 {
        let raw = self.finalize_raw();

        // Everything down below is a permutation, so it does not affect
        // collision probability.
        let mut lo = (raw as u64).wrapping_add(tweak);
        let mut hi = (raw >> 64) as u64;

        // Somewhat inspired by https://jonkagstrom.com/mx3/mx3_rev2.html.
        lo ^= lo >> 32;
        lo = lo.wrapping_mul(0xe9846af9b1a615d);
        hi ^= hi >> 32;
        hi = hi.wrapping_mul(0xe9846af9b1a615d);
        lo ^= hi.rotate_left(32);
        hi = hi.wrapping_add(lo);
        lo ^= lo >> 32;
        lo = lo.wrapping_mul(0xe9846af9b1a615d);
        hi ^= hi >> 32;
        hi = hi.wrapping_mul(0xe9846af9b1a615d);

        // Multiplying by the independent secret `avalanche_mul` restores
        // almost-XOR-universality. It also provides the final diffusion and
        // makes the whole structure much harder to invert should outputs leak.
        gf128mul(((lo as u128) << 64) | hi as u128, self.params.avalanche_mul)
    }

    /// Returns a 128-bit tag forming a message authentication code.
    ///
    /// Note: the top two bits of the nonce are ignored. If the 126-bit nonce is
    /// re-used with the same message an attacker can detect duplicate messages.
    ///
    /// Assuming AES-128 is a secure pseudorandom permutation, for messages of
    /// at most 1 GiB the forgery probability stays below 2<sup>-50</sup> for up
    /// to 2<sup>54</sup> tags, of which up to 2<sup>27</sup> may reuse a nonce.
    /// See Theorem 2 of <https://eprint.iacr.org/2020/1145> for the general
    /// bound.
    ///
    /// # Panics
    ///
    /// Panics if the [`PolyXor128`] instance was created without an AES key,
    /// i.e. through [`from_entropy`](PolyXor128::from_entropy).
    #[cfg(feature = "aes")]
    #[must_use]
    pub fn finalize_mac(&self, nonce: u128) -> u128 {
        let aes_key = self
            .params
            .aes_key
            .as_ref()
            .expect("PolyXOR128 must be initialized with AES key to use finalize_mac");

        // Nonce-based Enhanced Hash-then-Mask: https://eprint.iacr.org/2020/1145
        // We toss away two bits from the nonce and hash to make each encrypt
        // call a unique domain (with the other calls happening during key
        // expansion).
        let mask = u128::MAX >> 2;
        let raw = self.finalize_raw();
        let mut blocks = [
            Array::from((nonce & mask).to_le_bytes()),
            Array::from((((raw ^ nonce) & mask) | (1 << 126)).to_le_bytes()),
        ];
        aes_key.encrypt_blocks(&mut blocks);
        let [b0, b1] = blocks;
        u128::from_le_bytes(b0.into()) ^ u128::from_le_bytes(b1.into())
    }

    /// Resets this hasher to the initial (empty-input) state.
    pub fn reset(&mut self) {
        #[cfg(feature = "zeroize")]
        self.zeroize_sponge();

        self.count = 0;
        self.poly_accum = self.params.poly_z;
    }

    /// Number of bytes hashed so far.
    #[must_use]
    pub fn count(&self) -> u64 {
        self.count
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vectors_from_entropy() {
        let entropy: [u8; PolyXor128::entropy_needed()] =
            core::array::from_fn(|i| (i * 7 + 3) as u8);
        let long: [u8; 5000] = core::array::from_fn(|i| i as u8);
        let tweak = 0x0123_4567_89ab_cdef;
        let cases: [(&[u8], u128, u128, u128); 3] = [
            (
                b"",
                0x71674dc8618a59aea5e747e3e8e65cb1,
                0x18e17e168ebb1e2546333eedd3e8d4cb,
                0x463831961cbb78bc09b4e223ae762653,
            ),
            (
                b"abc",
                0x768ec4cb13ed00df813dd5a56ee735c7,
                0x9d8c4cf7c0441c2ea888298e36e23a2b,
                0xad828d5044a86b58b3099cff9bd00846,
            ),
            (
                &long,
                0xf7d15316f72aa4bafac50b723c904dba,
                0xdc08376d948de1d510b80d819ca6f4de,
                0x7b52a8346b7c0a938f0333c3b57c85a3,
            ),
        ];

        let params = PolyXor128::from_entropy(&entropy);
        for (msg, raw, full, tweaked) in cases {
            let mut h = params.hasher();
            h.update(msg);
            assert_eq!(h.finalize_raw(), raw);
            assert_eq!(h.finalize_avalanche(), full);
            assert_eq!(h.finalize_avalanche_with_tweak(tweak), tweaked);
        }
    }

    #[cfg(feature = "aes")]
    #[test]
    fn test_vectors_from_key() {
        let key = 0x0123_4567_89ab_cdef_fedc_ba98_7654_3210;
        let long: [u8; 5000] = core::array::from_fn(|i| i as u8);
        let cases: [(&[u8], u128, u128); 3] = [
            (
                b"",
                0x848d40b38af689d1bf33645504916ccf,
                0x1ddadfc23088181c7772364ac0693d8c,
            ),
            (
                b"abc",
                0xc50ca7f96a0eeafd827bc6e264cda461,
                0x9f561bc3356a93411738fb36838c5dda,
            ),
            (
                &long,
                0x569abc56a85b9928d5616e900ebd9eb9,
                0x05edacb22bf0eccb88d0344b97f2b485,
            ),
        ];

        let params = PolyXor128::from_key(key);
        for (msg, raw, mac) in cases {
            let mut h = params.hasher();
            h.update(msg);
            assert_eq!(h.finalize_raw(), raw);
            assert_eq!(h.finalize_mac(42), mac);
        }
    }
}
