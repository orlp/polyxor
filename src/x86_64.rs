//! AVX, AVX2 and AVX-512 implementations of [`crate::reference::hash_blocks`].
//!
//! Technically the AVX implementation doesn't need AVX, only PCLMULQDQ, but
//! adding AVX on top adds more efficient instruction encoding and excludes only
//! a very small handful of old processors.

use core::arch::x86_64::{
    _mm_clmulepi64_si128 as clmul, _mm_load_si128 as load128, _mm_loadu_si128 as loadu128,
    _mm256_clmulepi64_epi128 as clmul256, _mm256_load_si256 as load256,
    _mm256_loadu_si256 as loadu256, _mm512_clmulepi64_epi128 as clmul512,
    _mm512_load_si512 as load512, _mm512_loadu_si512 as loadu512, *,
};

use crate::PolyXor128;

#[inline]
#[target_feature(enable = "avx,pclmulqdq")]
fn gf128mul(a: __m128i, b: __m128i) -> __m128i {
    // Karatsuba.
    let modulus = _mm_set_epi64x(0, 0xc200_0000_0000_0000u64 as i64);
    let ll = clmul(a, b, 0x00);
    let hh = clmul(a, b, 0x11);
    let a_sum = _mm_xor_si128(a, _mm_srli_si128(a, 8));
    let b_sum = _mm_xor_si128(b, _mm_srli_si128(b, 8));
    let mid = _mm_xor_si128(clmul(a_sum, b_sum, 0x00), _mm_xor_si128(ll, hh));
    let lo = _mm_xor_si128(ll, _mm_slli_si128(mid, 8));
    let hi = _mm_xor_si128(hh, _mm_srli_si128(mid, 8));

    // Montgomery reduction.
    let fold_lo = clmul(lo, modulus, 0x00);
    let lo = _mm_xor_si128(_mm_shuffle_epi32(fold_lo, 0x4e), lo);
    let fold_hi = clmul(lo, modulus, 0x01);
    _mm_xor_si128(_mm_xor_si128(fold_hi, lo), hi)
}

#[target_feature(enable = "avx,pclmulqdq")]
pub fn gf128mul_u128(a: u128, b: u128) -> u128 {
    unsafe {
        let mut out = 0u128;
        let av = loadu128((&raw const a).cast());
        let bv = loadu128((&raw const b).cast());
        _mm_storeu_si128((&raw mut out).cast(), gf128mul(av, bv));
        out
    }
}

// One 128-byte block per iteration.
#[target_feature(enable = "avx,pclmulqdq")]
pub fn hash_blocks_avx(mut data: &[u8], params: &PolyXor128, poly_accum: &mut u128) {
    unsafe {
        let poly_u = loadu128((&raw const params.poly_u).cast());
        let poly_y = loadu128((&raw const params.poly_y).cast());
        let zero = _mm_setzero_si128();
        let mut p = loadu128((&raw const *poly_accum).cast());

        let entropy = &params.block_key.0;
        while data.len() >= 128 {
            let (mut ha, mut hb, mut hc, mut hd, mut he) = (zero, zero, zero, zero, zero);

            let blocks = (data.len() / 128).min(entropy.len() / 128);
            let mut key = entropy.as_ptr().cast::<__m128i>();
            let mut m = data.as_ptr().cast::<__m128i>();
            for _ in 0..blocks {
                let r0 = _mm_xor_si128(loadu128(m), load128(key));
                let r1 = _mm_xor_si128(loadu128(m.add(1)), load128(key.add(1)));
                let r2 = _mm_xor_si128(loadu128(m.add(2)), load128(key.add(2)));
                let r3 = _mm_xor_si128(loadu128(m.add(3)), load128(key.add(3)));
                let r4 = _mm_xor_si128(loadu128(m.add(4)), load128(key.add(4)));
                let r5 = _mm_xor_si128(loadu128(m.add(5)), load128(key.add(5)));
                let r6 = _mm_xor_si128(loadu128(m.add(6)), load128(key.add(6)));
                let r7 = _mm_xor_si128(loadu128(m.add(7)), load128(key.add(7)));
                let e0 = _mm_xor_si128(_mm_xor_si128(r0, r1), _mm_xor_si128(r4, r5));
                let e1 = _mm_xor_si128(_mm_xor_si128(r2, r3), _mm_xor_si128(r6, r7));

                ha = _mm_xor_si128(ha, _mm_xor_si128(clmul(r0, r6, 0x00), clmul(r0, r6, 0x11)));
                hb = _mm_xor_si128(hb, _mm_xor_si128(clmul(r1, r7, 0x00), clmul(r1, r7, 0x11)));
                hc = _mm_xor_si128(hc, _mm_xor_si128(clmul(r4, r2, 0x00), clmul(r4, r2, 0x11)));
                hd = _mm_xor_si128(hd, _mm_xor_si128(clmul(r5, r3, 0x00), clmul(r5, r3, 0x11)));
                he = _mm_xor_si128(he, _mm_xor_si128(clmul(e0, e1, 0x00), clmul(e0, e1, 0x11)));

                m = m.add(8);
                key = key.add(8);
            }
            data = &data[blocks * 128..];

            let hcd = _mm_xor_si128(hc, hd);
            let hcd_swapped = _mm_shuffle_epi32(hcd, 0b10_11_00_01);
            let high_dwords = _mm_set1_epi64x(0xffff_ffff_0000_0000u64 as i64);
            let whcd = _mm_xor_si128(hcd_swapped, _mm_and_si128(hcd, high_dwords));
            let h0 = _mm_xor_si128(_mm_xor_si128(ha, hb), hcd);
            let h1 = _mm_xor_si128(_mm_xor_si128(hb, hd), _mm_xor_si128(he, whcd));
            p = _mm_xor_si128(
                gf128mul(_mm_xor_si128(p, poly_u), _mm_xor_si128(h1, poly_y)),
                h0,
            );
        }

        _mm_storeu_si128((&raw mut *poly_accum).cast(), p);
    }
}

// Two 128-byte blocks per iteration, with a single-block tail, using the
// 256-bit (VEX) VPCLMULQDQ found on CPUs without AVX-512 such as Zen 3 and
// Alder Lake.
#[target_feature(enable = "avx2,vpclmulqdq")]
pub fn hash_blocks_avx2(mut data: &[u8], params: &PolyXor128, poly_accum: &mut u128) {
    unsafe {
        let poly_u = loadu128((&raw const params.poly_u).cast());
        let poly_y = loadu128((&raw const params.poly_y).cast());
        let zero = _mm256_setzero_si256();
        let mut p = loadu128((&raw const *poly_accum).cast());

        let entropy = &params.block_key.0;
        while data.len() >= 128 {
            // acc_ab contains ha, hb and acc_cd contains hc, hd.
            let (mut acc_ab, mut acc_cd, mut acc_e) = (zero, zero, zero);

            let blocks = (data.len() / 128).min(entropy.len() / 128);
            let mut key = entropy.as_ptr().cast::<__m256i>();
            let mut m = data.as_ptr().cast::<__m256i>();
            for _ in 0..blocks / 2 {
                // [r0, r1], [r2, r3], [r4, r5], [r6, r7] for both blocks.
                let y0 = _mm256_xor_si256(loadu256(m), load256(key));
                let y1 = _mm256_xor_si256(loadu256(m.add(1)), load256(key.add(1)));
                let y2 = _mm256_xor_si256(loadu256(m.add(2)), load256(key.add(2)));
                let y3 = _mm256_xor_si256(loadu256(m.add(3)), load256(key.add(3)));
                let y4 = _mm256_xor_si256(loadu256(m.add(4)), load256(key.add(4)));
                let y5 = _mm256_xor_si256(loadu256(m.add(5)), load256(key.add(5)));
                let y6 = _mm256_xor_si256(loadu256(m.add(6)), load256(key.add(6)));
                let y7 = _mm256_xor_si256(loadu256(m.add(7)), load256(key.add(7)));

                let ab0 = _mm256_xor_si256(clmul256::<0x00>(y0, y3), clmul256::<0x11>(y0, y3));
                let cd0 = _mm256_xor_si256(clmul256::<0x00>(y2, y1), clmul256::<0x11>(y2, y1));
                let ab1 = _mm256_xor_si256(clmul256::<0x00>(y4, y7), clmul256::<0x11>(y4, y7));
                let cd1 = _mm256_xor_si256(clmul256::<0x00>(y6, y5), clmul256::<0x11>(y6, y5));
                acc_ab = _mm256_xor_si256(acc_ab, _mm256_xor_si256(ab0, ab1));
                acc_cd = _mm256_xor_si256(acc_cd, _mm256_xor_si256(cd0, cd1));

                // Each block's e0 and e1 are split over both lanes. Combine
                // them so e0 and e1 hold the first block in the low lane and
                // the second block in the high lane.
                let (e00, e10) = (_mm256_xor_si256(y0, y2), _mm256_xor_si256(y1, y3));
                let (e01, e11) = (_mm256_xor_si256(y4, y6), _mm256_xor_si256(y5, y7));
                let e0 = _mm256_xor_si256(
                    _mm256_blend_epi32::<0xf0>(e00, e01),
                    _mm256_permute2x128_si256::<0x21>(e00, e01),
                );
                let e1 = _mm256_xor_si256(
                    _mm256_blend_epi32::<0xf0>(e10, e11),
                    _mm256_permute2x128_si256::<0x21>(e10, e11),
                );
                let e = _mm256_xor_si256(clmul256::<0x00>(e0, e1), clmul256::<0x11>(e0, e1));
                acc_e = _mm256_xor_si256(acc_e, e);

                m = m.add(8);
                key = key.add(8);
            }

            // Odd trailing block. Same as above just with an all-zero second block.
            if blocks % 2 == 1 {
                let y0 = _mm256_xor_si256(loadu256(m), load256(key));
                let y1 = _mm256_xor_si256(loadu256(m.add(1)), load256(key.add(1)));
                let y2 = _mm256_xor_si256(loadu256(m.add(2)), load256(key.add(2)));
                let y3 = _mm256_xor_si256(loadu256(m.add(3)), load256(key.add(3)));

                let ab = _mm256_xor_si256(clmul256::<0x00>(y0, y3), clmul256::<0x11>(y0, y3));
                let cd = _mm256_xor_si256(clmul256::<0x00>(y2, y1), clmul256::<0x11>(y2, y1));
                acc_ab = _mm256_xor_si256(acc_ab, ab);
                acc_cd = _mm256_xor_si256(acc_cd, cd);

                let (e00, e10) = (_mm256_xor_si256(y0, y2), _mm256_xor_si256(y1, y3));
                let e0 = _mm256_xor_si256(
                    _mm256_blend_epi32::<0xf0>(e00, zero),
                    _mm256_permute2x128_si256::<0x21>(e00, zero),
                );
                let e1 = _mm256_xor_si256(
                    _mm256_blend_epi32::<0xf0>(e10, zero),
                    _mm256_permute2x128_si256::<0x21>(e10, zero),
                );
                let e = _mm256_xor_si256(clmul256::<0x00>(e0, e1), clmul256::<0x11>(e0, e1));
                acc_e = _mm256_xor_si256(acc_e, e);
            }
            data = &data[blocks * 128..];

            let ha = _mm256_castsi256_si128(acc_ab);
            let hb = _mm256_extracti128_si256::<1>(acc_ab);
            let hc = _mm256_castsi256_si128(acc_cd);
            let hd = _mm256_extracti128_si256::<1>(acc_cd);
            let he = _mm_xor_si128(
                _mm256_castsi256_si128(acc_e),
                _mm256_extracti128_si256::<1>(acc_e),
            );

            let hcd = _mm_xor_si128(hc, hd);
            let hcd_swapped = _mm_shuffle_epi32(hcd, 0b10_11_00_01);
            let high_dwords = _mm_set1_epi64x(0xffff_ffff_0000_0000u64 as i64);
            let whcd = _mm_xor_si128(hcd_swapped, _mm_and_si128(hcd, high_dwords));
            let h0 = _mm_xor_si128(_mm_xor_si128(ha, hb), hcd);
            let h1 = _mm_xor_si128(_mm_xor_si128(hb, hd), _mm_xor_si128(he, whcd));
            p = _mm_xor_si128(
                gf128mul(_mm_xor_si128(p, poly_u), _mm_xor_si128(h1, poly_y)),
                h0,
            );
        }

        _mm_storeu_si128((&raw mut *poly_accum).cast(), p);
    }
}

// Two 128-byte blocks per iteration, with a single-block tail.
// avx512vl is enabled for better codegen, even if not strictly needed, implied
// realistically by avx512f + vpclmulqdq anyway.
#[target_feature(enable = "avx512f,avx512vl,vpclmulqdq")]
pub fn hash_blocks_avx512(mut data: &[u8], params: &PolyXor128, poly_accum: &mut u128) {
    const TERNLOG_XOR3: i32 = 0b1001_0110;

    unsafe {
        let poly_u = loadu128((&raw const params.poly_u).cast());
        let poly_y = loadu128((&raw const params.poly_y).cast());
        let mut p = loadu128((&raw const *poly_accum).cast());

        let zero = _mm512_setzero_si512();
        let idx_lo = _mm512_setr_epi64(0, 4, 1, 5, 8, 12, 9, 13);
        let idx_hi = _mm512_setr_epi64(2, 6, 3, 7, 10, 14, 11, 15);

        let entropy = &params.block_key.0;
        while data.len() >= 128 {
            // acc0, acc1 both contain ha, hb, hc, hd in that order. Two
            // accumulators for speed.
            let (mut acc0, mut acc1, mut acc_e) = (zero, zero, zero);
            let blocks = (data.len() / 128).min(entropy.len() / 128);
            let mut key = entropy.as_ptr().cast::<__m512i>();
            let mut m = data.as_ptr().cast::<__m512i>();
            for _ in 0..blocks / 2 {
                let z0 = _mm512_xor_si512(loadu512(m), load512(key));
                let z1 = _mm512_xor_si512(loadu512(m.add(1)), load512(key.add(1)));
                let z2 = _mm512_xor_si512(loadu512(m.add(2)), load512(key.add(2)));
                let z3 = _mm512_xor_si512(loadu512(m.add(3)), load512(key.add(3)));

                let z1s = _mm512_shuffle_i64x2::<0b01_00_11_10>(z1, z1);
                let z3s = _mm512_shuffle_i64x2::<0b01_00_11_10>(z3, z3);
                let (z01l, z01h) = (clmul512::<0x00>(z0, z1s), clmul512::<0x11>(z0, z1s));
                let (z23l, z23h) = (clmul512::<0x00>(z2, z3s), clmul512::<0x11>(z2, z3s));
                acc0 = _mm512_ternarylogic_epi64::<TERNLOG_XOR3>(acc0, z01l, z01h);
                acc1 = _mm512_ternarylogic_epi64::<TERNLOG_XOR3>(acc1, z23l, z23h);

                let xz01 = _mm512_xor_si512(z0, z1);
                let xz23 = _mm512_xor_si512(z2, z3);
                let x0123l = _mm512_permutex2var_epi64(xz01, idx_lo, xz23);
                let x0123h = _mm512_permutex2var_epi64(xz01, idx_hi, xz23);
                let x0123 = _mm512_xor_si512(x0123l, x0123h);
                acc_e = _mm512_xor_si512(acc_e, clmul512::<0x01>(x0123, x0123));

                m = m.add(4);
                key = key.add(4);
            }

            // Odd trailing block. Same as above just with full-zero second half.
            if blocks % 2 == 1 {
                let z0 = _mm512_xor_si512(loadu512(m), load512(key));
                let z1 = _mm512_xor_si512(loadu512(m.add(1)), load512(key.add(1)));

                let z1s = _mm512_shuffle_i64x2::<0b01_00_11_10>(z1, z1);
                let (z01l, z01h) = (clmul512::<0x00>(z0, z1s), clmul512::<0x11>(z0, z1s));
                acc0 = _mm512_ternarylogic_epi64::<TERNLOG_XOR3>(acc0, z01l, z01h);

                let xz01 = _mm512_xor_si512(z0, z1);
                let x01l = _mm512_permutex2var_epi64(xz01, idx_lo, zero);
                let x01h = _mm512_permutex2var_epi64(xz01, idx_hi, zero);
                let x01 = _mm512_xor_si512(x01l, x01h);
                acc_e = _mm512_xor_si512(acc_e, clmul512::<0x01>(x01, x01));
            }
            data = &data[blocks * 128..];

            let acc = _mm512_xor_si512(acc0, acc1);
            let acc_lo = _mm512_castsi512_si256(acc);
            let acc_hi = _mm512_extracti64x4_epi64::<1>(acc);
            let e_lo = _mm512_castsi512_si256(acc_e);
            let e_hi = _mm512_extracti64x4_epi64::<1>(acc_e);
            let acc_e256 = _mm256_xor_si256(e_lo, e_hi);
            let ha = _mm256_castsi256_si128(acc_lo);
            let hb = _mm256_extracti128_si256::<1>(acc_lo);
            let hc = _mm256_castsi256_si128(acc_hi);
            let hd = _mm256_extracti128_si256::<1>(acc_hi);
            let he = _mm_xor_si128(
                _mm256_castsi256_si128(acc_e256),
                _mm256_extracti128_si256::<1>(acc_e256),
            );

            let hcd = _mm_xor_si128(hc, hd);
            let hcd_swapped = _mm_shuffle_epi32(hcd, 0b10_11_00_01);
            let high_dwords = _mm_set1_epi64x(0xffff_ffff_0000_0000u64 as i64);
            let whcd = _mm_xor_si128(hcd_swapped, _mm_and_si128(hcd, high_dwords));
            let h0 = _mm_xor_si128(_mm_xor_si128(ha, hb), hcd);
            let h1 = _mm_xor_si128(_mm_xor_si128(hb, hd), _mm_xor_si128(he, whcd));
            p = _mm_xor_si128(
                gf128mul(_mm_xor_si128(p, poly_u), _mm_xor_si128(h1, poly_y)),
                h0,
            );
        }

        _mm_storeu_si128((&raw mut *poly_accum).cast(), p);
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use std::arch::is_x86_feature_detected as has_feat;

    use crate::reference::testing::{check_gf128mul, check_hash_blocks};

    #[test]
    fn avx_matches_reference() {
        if has_feat!("avx") && has_feat!("pclmulqdq") {
            check_gf128mul(super::gf128mul_u128);
            check_hash_blocks(super::hash_blocks_avx);
        }
    }

    #[test]
    fn avx2_matches_reference() {
        if has_feat!("avx2") && has_feat!("vpclmulqdq") {
            check_hash_blocks(super::hash_blocks_avx2);
        }
    }

    #[test]
    fn avx512_matches_reference() {
        if has_feat!("avx512f") && has_feat!("avx512vl") && has_feat!("vpclmulqdq") {
            check_hash_blocks(super::hash_blocks_avx512);
        }
    }
}
