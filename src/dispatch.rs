//! Runtime and compile-time selection of the best `hash_blocks` / `gf128mul`.

use crate::PolyXor128;

#[allow(dead_code)]
type HashBlocksFn = unsafe fn(&[u8], &PolyXor128, &mut u128);
#[allow(dead_code)]
type Gf128MulFn = unsafe fn(u128, u128) -> u128;

#[cfg(feature = "runtime_detection")]
#[allow(dead_code)]
fn get_hash_blocks_fn() -> HashBlocksFn {
    cfg_select! {
        target_arch = "x86_64" => {
            use std::arch::is_x86_feature_detected as has_feat;

            if has_feat!("avx512f") && has_feat!("avx512vl") && has_feat!("vpclmulqdq") {
                return crate::x86_64::hash_blocks_avx512;
            }

            if has_feat!("avx2") && has_feat!("vpclmulqdq") {
                return crate::x86_64::hash_blocks_avx2;
            }

            if has_feat!("avx") && has_feat!("pclmulqdq") {
                return crate::x86_64::hash_blocks_avx;
            }
        },
        target_arch = "aarch64" => {
            use std::arch::is_aarch64_feature_detected as has_feat;

            if has_feat!("neon") && has_feat!("aes") {
                return crate::neon::hash_blocks;
            }
        },
        _ => {},
    }

    crate::reference::hash_blocks
}

#[cfg(feature = "runtime_detection")]
#[allow(dead_code)]
fn get_gf128mul_fn() -> Gf128MulFn {
    cfg_select! {
        target_arch = "x86_64" => {
            use std::arch::is_x86_feature_detected as has_feat;

            if has_feat!("avx") && has_feat!("pclmulqdq") {
                return crate::x86_64::gf128mul_u128;
            }
        },
        target_arch = "aarch64" => {
            use std::arch::is_aarch64_feature_detected as has_feat;

            if has_feat!("neon") && has_feat!("aes") {
                return crate::neon::gf128mul_u128;
            }
        },
        _ => {},
    }

    crate::reference::gf128mul
}

#[inline]
pub fn hash_blocks(data: &[u8], params: &PolyXor128, poly_accum: &mut u128) {
    debug_assert!(data.len().is_multiple_of(crate::INNER_BLOCK_SIZE));

    cfg_select! {
        all(
            target_arch = "aarch64",
            target_feature = "neon",
            target_feature = "aes"
        ) => unsafe { crate::neon::hash_blocks(data, params, poly_accum) },

        all(
            target_arch = "x86_64",
            target_feature = "avx512f",
            target_feature = "avx512vl",
            target_feature = "vpclmulqdq"
        ) => unsafe { crate::x86_64::hash_blocks_avx512(data, params, poly_accum) },

        // With runtime detection we'd rather check for better instruction sets at runtime,
        // unless there is nothing better to find.
        all(
            not(feature = "runtime_detection"),
            target_arch = "x86_64",
            target_feature = "avx2",
            target_feature = "vpclmulqdq"
        ) => unsafe { crate::x86_64::hash_blocks_avx2(data, params, poly_accum) },

        all(
            not(feature = "runtime_detection"),
            target_arch = "x86_64",
            target_feature = "avx",
            target_feature = "pclmulqdq"
        ) => unsafe { crate::x86_64::hash_blocks_avx(data, params, poly_accum) },

        all(
            feature = "runtime_detection",
            any(target_arch = "x86_64", target_arch = "aarch64")
        ) => unsafe {
            use core::sync::atomic::{AtomicPtr, Ordering};

            fn init_f(data: &[u8], params: &PolyXor128, poly_accum: &mut u128) {
                let f = get_hash_blocks_fn();
                HASH_BLOCKS_FN.store(f as *mut (), Ordering::Relaxed);
                unsafe { f(data, params, poly_accum) }
            }

            static HASH_BLOCKS_FN: AtomicPtr<()> = AtomicPtr::new(init_f as *mut ());
            let f: HashBlocksFn = core::mem::transmute(HASH_BLOCKS_FN.load(Ordering::Relaxed));
            f(data, params, poly_accum)
        },

        _ => crate::reference::hash_blocks(data, params, poly_accum),
    }
}

#[inline]
pub fn gf128mul(x: u128, y: u128) -> u128 {
    cfg_select! {
        all(
            target_arch = "aarch64",
            target_feature = "neon",
            target_feature = "aes"
        ) => unsafe { crate::neon::gf128mul_u128(x, y) },

        all(
            target_arch = "x86_64",
            target_feature = "avx",
            target_feature = "pclmulqdq"
        ) => unsafe { crate::x86_64::gf128mul_u128(x, y) },

        all(
            feature = "runtime_detection",
            any(target_arch = "x86_64", target_arch = "aarch64")
        ) => unsafe {
            use core::sync::atomic::{AtomicPtr, Ordering};

            fn init_f(x: u128, y: u128) -> u128 {
                let f = get_gf128mul_fn();
                GF128MUL_FN.store(f as *mut (), Ordering::Relaxed);
                unsafe { f(x, y) }
            }

            static GF128MUL_FN: AtomicPtr<()> = AtomicPtr::new(init_f as *mut ());
            let f: Gf128MulFn = core::mem::transmute(GF128MUL_FN.load(Ordering::Relaxed));
            f(x, y)
        },

        _ => crate::reference::gf128mul(x, y),
    }
}
