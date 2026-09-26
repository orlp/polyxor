use crate::PolyXor128;

fn loadle64(bytes: &[u8]) -> u64 {
    u64::from_le_bytes(bytes[0..8].try_into().unwrap())
}

// Carryless, widening multiplication.
fn clmul(mut x: u64, y: u64) -> u128 {
    let mut out = 0u128;
    for _ in 0..64 {
        out <<= 1;
        let mask = ((x as i64) >> 63) as u64;
        out ^= (mask & y) as u128;
        x <<= 1;
    }
    out
}

// GF(2^128) multiplication (POLYVAL's x^128 + x^127 + x^126 + x^121 + 1 Montgomery form).
pub(crate) fn gf128mul(a: u128, b: u128) -> u128 {
    const POLY: u64 = 0xc200_0000_0000_0000;
    let (al, ah) = (a as u64, (a >> 64) as u64);
    let (bl, bh) = (b as u64, (b >> 64) as u64);
    let ll = clmul(al, bl);
    let hh = clmul(ah, bh);
    let mid = clmul(al ^ ah, bl ^ bh) ^ ll ^ hh;
    let lo = ll ^ (mid << 64);
    let hi = hh ^ (mid >> 64);

    let fold_lo = clmul(lo as u64, POLY);
    let lo = lo ^ fold_lo.rotate_left(64);
    let fold_hi = clmul((lo >> 64) as u64, POLY);
    fold_hi ^ lo ^ hi
}

// Treat x as GF(4)^64, with 32-bit subwords [lo0, hi0, lo1, hi1], where
// lo0 contains the low bits of the first 32 GF(4) elements, hi0 contains the
// respective high bits of those elements, and similarly for lo1, hi1.
// Then, multiply each element by generator w.
fn gf4mul_w(x: u128) -> u128 {
    let lo_dwords = 0x0000_0000_ffff_ffff_0000_0000_ffff_ffffu128;
    let swapped = ((x & lo_dwords) << 32) | ((x >> 32) & lo_dwords);
    swapped ^ (x & !lo_dwords)
}

// Assuming a, b, c, d have been XOR'd with independent keys, 2^-128 AXU.
fn compress_axu128(a: [u64; 2], b: [u64; 2], c: [u64; 2], d: [u64; 2]) -> (u128, u128) {
    // Very similar to Nandi's encode-hash-combine, except we don't provide
    // extra key material for e. Not generally allowed - this needed a separate
    // proof.
    let e = [a[0] ^ b[0] ^ c[0] ^ d[0], a[1] ^ b[1] ^ c[1] ^ d[1]];
    let ha = clmul(a[0], a[1]);
    let hb = clmul(b[0], b[1]);
    let hc = clmul(c[0], c[1]);
    let hd = clmul(d[0], d[1]);
    let he = clmul(e[0], e[1]);

    // Combine with matrix where each 2x2 submatrix has non-zero determinant.
    //   h0 = (1 1 1  1   0) (ha hb hc hd he)^T
    //   h1 = (0 1 w  w^2 1) (ha hb hc hd he)^T
    // Note that this combination procedure completely distributes over XOR,
    // meaning in non-reference code one should accumulate ha, ..., he, and only
    // combine at the end. Also, in GF(4) we have w^2 = w + 1, giving
    // w*hc + w^2*hd = w*(hc + hd) + hd.
    let h0 = ha ^ hb ^ hc ^ hd;
    let h1 = hb ^ gf4mul_w(hc ^ hd) ^ hd ^ he;
    (h0, h1)
}

fn hash_block(data: &[u8; 128], entropy: &[u8; 128]) -> (u128, u128) {
    // Two parallel (8 * u64) -> (4 * u64) 2^-128 AXU universal hashes, combined
    // with XOR. One on the even elements, one on the odd.
    let m: [u64; 16] = core::array::from_fn(|i| {
        loadle64(&data[8 * i..8 * (i + 1)]) ^ loadle64(&entropy[8 * i..8 * (i + 1)])
    });
    let (h0_even, h1_even) =
        compress_axu128([m[0], m[12]], [m[2], m[14]], [m[8], m[4]], [m[10], m[6]]);
    let (h0_odd, h1_odd) =
        compress_axu128([m[1], m[13]], [m[3], m[15]], [m[9], m[5]], [m[11], m[7]]);
    (h0_even ^ h0_odd, h1_even ^ h1_odd)
}

pub(crate) fn hash_blocks(mut data: &[u8], params: &PolyXor128, poly_accum: &mut u128) {
    let entropy = &params.block_key.0;
    while data.len() >= 128 {
        let mut h0 = 0;
        let mut h1 = 0;
        let blocks = (data.len() / 128).min(entropy.len() / 128);
        for i in 0..blocks {
            let data_block = data[128 * i..128 * (i + 1)].try_into().unwrap();
            let entropy_block = entropy[128 * i..128 * (i + 1)].try_into().unwrap();
            let (th0, th1) = hash_block(data_block, entropy_block);
            h0 ^= th0;
            h1 ^= th1;
        }
        data = &data[blocks * 128..];

        *poly_accum = gf128mul(*poly_accum ^ params.poly_u, h1 ^ params.poly_y) ^ h0;
    }
}

/// Helpers for testing other backends against this reference.
#[cfg(test)]
#[allow(dead_code)] // Unused on targets without other backends.
pub(crate) mod testing {
    extern crate std;
    use std::vec::Vec;

    use super::*;
    use crate::{INNER_BLOCK_SIZE, OUTER_BLOCK_SIZE};

    fn pseudo_random_bytes(n: usize, seed: u64) -> Vec<u8> {
        // Top byte of a 64-bit LCG.
        let mut x = seed;
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            x = x.wrapping_mul(0x5851_f42d_4c95_7f2d).wrapping_add(1);
            out.push((x >> 56) as u8);
        }
        out
    }

    pub(crate) fn check_gf128mul(f: unsafe fn(u128, u128) -> u128) {
        let bytes = pseudo_random_bytes(16 * 64, 1);
        let (vals, _) = bytes.as_chunks();
        for a in vals {
            for b in vals {
                let (a, b) = (u128::from_le_bytes(*a), u128::from_le_bytes(*b));
                assert_eq!(unsafe { f(a, b) }, gf128mul(a, b), "a={a:#x}, b={b:#x}");
            }
        }
    }

    pub(crate) fn check_hash_blocks(f: unsafe fn(&[u8], &PolyXor128, &mut u128)) {
        let entropy = pseudo_random_bytes(PolyXor128::entropy_needed(), 2);
        let params = PolyXor128::from_entropy(&entropy);
        let buf = pseudo_random_bytes(1 + 3 * OUTER_BLOCK_SIZE + INNER_BLOCK_SIZE, 3);
        let data = &buf[1..]; // Deliberately unaligned.
        for blocks in 0..=data.len() / INNER_BLOCK_SIZE {
            let data = &data[..blocks * INNER_BLOCK_SIZE];
            let (mut expected, mut actual) = (params.poly_z, params.poly_z);
            hash_blocks(data, &params, &mut expected);
            unsafe { f(data, &params, &mut actual) };
            assert_eq!(actual, expected, "{blocks} blocks");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn polyval_test_vector() {
        // RFC 8452, Appendix A: POLYVAL(H, X_1, X_2).
        let h = 0x7b754bba26f8311d7642925847936225;
        let x1 = 0x62a2012dbb621740b6df838c66954f4f;
        let x2 = 0x62f3c9d3205fe4bb06d02127dd4da2d1;
        let expected = 0x7eb7e5f56c86b7e5fa1961847bb4a3f7;
        assert_eq!(gf128mul(gf128mul(x1, h) ^ x2, h), expected);
    }
}
