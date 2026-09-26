use std::fs::File;
use std::hash::{BuildHasher, Hasher};
use std::hint::black_box;
use std::io::Write;
use std::time::Instant;

use aegis::aegis128l::Aegis128LMac;
use poly1305::Poly1305;
use polyval::Polyval;
use polyval::universal_hash::{KeyInit, UniversalHash};
use polyxor::PolyXor128;
use sha1::Digest;

fn aligned_data(bytes: usize) -> (Vec<u8>, usize) {
    let mut buf = vec![0u8; bytes + 64];
    for (i, b) in buf.iter_mut().enumerate() {
        *b = i as u8;
    }
    let off = buf.as_ptr().align_offset(64);
    (buf, off)
}

fn speedtest<R, H: Fn(&[u8]) -> R>(bytes: usize, h: H) -> f64 {
    let (buf, off) = aligned_data(bytes);
    let data = &buf[off..off + bytes];

    // Aim for 0.1 second warm-up, then the best of five 0.1 second runs.
    let mut iters = 0;
    let start = Instant::now();
    loop {
        black_box(h(black_box(data)));
        iters += 1;

        let elapsed = start.elapsed().as_secs_f64();
        if elapsed >= 0.1 {
            break;
        }
    }

    let s_per_iter = start.elapsed().as_secs_f64() / iters as f64;
    let iters = (0.1 / s_per_iter).ceil() as u64;
    let mut best_ns = f64::INFINITY;
    for _ in 0..5 {
        let bench_start = Instant::now();
        for _ in 0..black_box(iters) {
            black_box(h(black_box(data)));
        }
        best_ns = best_ns.min(bench_start.elapsed().as_nanos() as f64 / iters as f64);
    }
    best_ns
}

fn bench<R, H: Fn(&[u8]) -> R>(csv: &mut Option<File>, name: &str, h: H) {
    println!("{name}");
    println!("{:>9}  {:>10}  {:>8}", "bytes", "ns", "GB/s");
    for n in 8..=24 {
        let sz = 1usize << n;
        let ns = speedtest(sz, &h);
        println!("{:>9}  {:>10.1}  {:>8.2}", sz, ns, sz as f64 / ns,);
        if let Some(f) = csv {
            writeln!(f, "{name},{sz},{ns}").unwrap();
        }
    }
    println!();
}

fn main() {
    // Usage: cargo bench --bench speed -- [out.csv]
    // Cargo itself passes --bench, so skip that.
    let mut csv = std::env::args()
        .skip(1)
        .find(|a| a != "--bench")
        .map(|path| {
            let mut f = File::create(path).unwrap();
            writeln!(f, "hash,bytes,ns").unwrap();
            f
        });

    let polyxor = PolyXor128::from_key(0x1234_5678_9abc_def0);
    bench(&mut csv, "polyxor128", |b| {
        let mut h = polyxor.hasher();
        h.update(b);
        h.finalize_raw()
    });

    bench(&mut csv, "polyxor128-mac", |b| {
        let mut h = polyxor.hasher();
        h.update(b);
        h.finalize_mac(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210)
    });

    let polyval = Polyval::new(&[0x42; 16].into());
    bench(&mut csv, "polyval", |b| {
        let mut h = polyval.clone();
        h.update_padded(b);
        h.finalize()
    });

    let poly1305 = Poly1305::new(&[0x42; 32].into());
    bench(&mut csv, "poly1305", |b| {
        poly1305.clone().compute_unpadded(b)
    });

    let aegis = Aegis128LMac::<16>::new(&[0x42; 16]);
    bench(&mut csv, "aegis-128l-mac", |b| {
        let mut h = aegis.clone();
        h.update(b);
        h.finalize()
    });

    let ahash = ahash::RandomState::with_seeds(1, 2, 3, 4);
    bench(&mut csv, "ahash", |b| {
        let mut h = ahash.build_hasher();
        h.write(b);
        h.finish()
    });

    let foldhash = foldhash::fast::FixedState::with_seed(0x1234);
    bench(&mut csv, "foldhash", |b| {
        let mut h = foldhash.build_hasher();
        h.write(b);
        h.finish()
    });

    bench(&mut csv, "blake3", blake3::hash);

    let rapidhash = rapidhash::v3::RapidSecrets::seed(0x1234);
    bench(&mut csv, "rapidhash", |b| {
        rapidhash::v3::rapidhash_v3_seeded(b, &rapidhash)
    });

    bench(&mut csv, "crc64-nvme", |b| {
        crc_fast::checksum(crc_fast::CrcAlgorithm::Crc64Nvme, b)
    });

    bench(&mut csv, "siphash2-4", |b| {
        let mut h = siphasher::sip::SipHasher24::new_with_keys(0x1234, 0x5678);
        h.write(b);
        h.finish()
    });

    let polymur = polymur_hash::PolymurHash::new(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210);
    bench(&mut csv, "polymur-hash", |b| polymur.hash(b));

    bench(&mut csv, "xxh3-128", |b| {
        twox_hash::XxHash3_128::oneshot_with_seed(0x1234, b)
    });

    bench(&mut csv, "sha1", |b| sha1::Sha1::digest(b));
}
