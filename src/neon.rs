//! NEON + FEAT_PMULL implementation of [`crate::reference::hash_blocks`].

use core::arch::aarch64::*;

use crate::PolyXor128;

#[inline]
#[target_feature(enable = "neon")]
unsafe fn load_u64x2(p: *const u8) -> uint64x2_t {
    let v = unsafe { p.cast::<uint64x2_t>().read() };
    cfg_select! {
        target_endian = "little" => v,
        _ => vreinterpretq_u64_u8(vrev64q_u8(vreinterpretq_u8_u64(v))),
    }
}

#[inline]
#[target_feature(enable = "neon")]
unsafe fn loadu_u64x2(p: *const u8) -> uint64x2_t {
    let v = unsafe { p.cast::<uint64x2_t>().read_unaligned() };
    cfg_select! {
        target_endian = "little" => v,
        _ => vreinterpretq_u64_u8(vrev64q_u8(vreinterpretq_u8_u64(v))),
    }
}

#[inline]
#[target_feature(enable = "neon")]
fn xor3(a: uint64x2_t, b: uint64x2_t, c: uint64x2_t) -> uint64x2_t {
    cfg_select! {
        target_feature = "sha3" => unsafe { veor3q_u64(a, b, c) },
        _ => veorq_u64(veorq_u64(a, b), c),
    }
}

#[inline]
#[target_feature(enable = "neon,aes")]
fn clmul_lo(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    vreinterpretq_u64_p128(vmull_p64(vgetq_lane_u64::<0>(a), vgetq_lane_u64::<0>(b)))
}

#[inline]
#[target_feature(enable = "neon,aes")]
fn clmul_hi(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    vreinterpretq_u64_p128(vmull_high_p64(
        vreinterpretq_p64_u64(a),
        vreinterpretq_p64_u64(b),
    ))
}

#[inline]
#[target_feature(enable = "neon,aes")]
fn gf128mul(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    // Karatsuba.
    let zero = vdupq_n_u64(0);
    let modulus = vdupq_n_u64(0xc200_0000_0000_0000);
    let ll = clmul_lo(a, b);
    let hh = clmul_hi(a, b);
    let a_sum = veorq_u64(a, vextq_u64::<1>(a, a));
    let b_sum = veorq_u64(b, vextq_u64::<1>(b, b));
    let mid = veorq_u64(clmul_lo(a_sum, b_sum), veorq_u64(ll, hh));
    let lo = veorq_u64(ll, vextq_u64::<1>(zero, mid));
    let hi = veorq_u64(hh, vextq_u64::<1>(mid, zero));

    // Montgomery reduction.
    let fold_lo = clmul_lo(lo, modulus);
    let lo = veorq_u64(vextq_u64::<1>(fold_lo, fold_lo), lo);
    let fold_hi = clmul_hi(lo, modulus);
    veorq_u64(veorq_u64(fold_hi, lo), hi)
}

#[target_feature(enable = "neon,aes")]
pub fn gf128mul_u128(a: u128, b: u128) -> u128 {
    vreinterpretq_p128_u64(gf128mul(
        vreinterpretq_u64_p128(a),
        vreinterpretq_u64_p128(b),
    ))
}

#[target_feature(enable = "neon,aes")]
pub fn hash_blocks(mut data: &[u8], params: &PolyXor128, poly_accum: &mut u128) {
    unsafe {
        let poly_u = vreinterpretq_u64_p128(params.poly_u);
        let poly_y = vreinterpretq_u64_p128(params.poly_y);
        let zero = vdupq_n_u64(0);
        let mut p = vreinterpretq_u64_p128(*poly_accum);

        let entropy = &params.block_key.0;
        while data.len() >= 128 {
            let (mut ha, mut hb, mut hc, mut hd, mut he) = (zero, zero, zero, zero, zero);

            let blocks = (data.len() / 128).min(entropy.len() / 128);
            let mut key = entropy.as_ptr();
            let mut d = data.as_ptr();
            for _ in 0..blocks {
                let r0 = veorq_u64(loadu_u64x2(d), load_u64x2(key));
                let r1 = veorq_u64(loadu_u64x2(d.add(16)), load_u64x2(key.add(16)));
                let r2 = veorq_u64(loadu_u64x2(d.add(32)), load_u64x2(key.add(32)));
                let r3 = veorq_u64(loadu_u64x2(d.add(48)), load_u64x2(key.add(48)));
                let r4 = veorq_u64(loadu_u64x2(d.add(64)), load_u64x2(key.add(64)));
                let r5 = veorq_u64(loadu_u64x2(d.add(80)), load_u64x2(key.add(80)));
                let r6 = veorq_u64(loadu_u64x2(d.add(96)), load_u64x2(key.add(96)));
                let r7 = veorq_u64(loadu_u64x2(d.add(112)), load_u64x2(key.add(112)));
                let e0 = veorq_u64(xor3(r0, r1, r4), r5);
                let e1 = veorq_u64(xor3(r2, r3, r6), r7);

                ha = xor3(ha, clmul_lo(r0, r6), clmul_hi(r0, r6));
                hb = xor3(hb, clmul_lo(r1, r7), clmul_hi(r1, r7));
                hc = xor3(hc, clmul_lo(r4, r2), clmul_hi(r4, r2));
                hd = xor3(hd, clmul_lo(r5, r3), clmul_hi(r5, r3));
                he = xor3(he, clmul_lo(e0, e1), clmul_hi(e0, e1));

                d = d.add(128);
                key = key.add(128);
            }
            data = &data[blocks * 128..];

            let hcd = veorq_u64(hc, hd);
            let hcd_swapped = vreinterpretq_u64_u32(vrev64q_u32(vreinterpretq_u32_u64(hcd)));
            let low_dwords = vdupq_n_u64(0x0000_0000_ffff_ffff);
            let whcd = veorq_u64(hcd_swapped, vbicq_u64(hcd, low_dwords));
            let h0 = xor3(ha, hb, hcd);
            let h1 = veorq_u64(xor3(hb, hd, he), whcd);
            p = veorq_u64(gf128mul(veorq_u64(p, poly_u), veorq_u64(h1, poly_y)), h0);
        }

        *poly_accum = vreinterpretq_p128_u64(p);
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use std::arch::is_aarch64_feature_detected as has_feat;

    use crate::reference::testing::{check_gf128mul, check_hash_blocks};

    #[test]
    fn matches_reference() {
        if has_feat!("neon") && has_feat!("aes") {
            check_gf128mul(super::gf128mul_u128);
            check_hash_blocks(super::hash_blocks);
        }
    }
}
