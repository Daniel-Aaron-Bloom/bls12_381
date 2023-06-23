#[macro_use]
extern crate criterion;

extern crate bls12_381;
use bls12_381::{*, fp::Fp, util};

use criterion::{black_box, Criterion};
use ff::Field;
use rand_core::SeedableRng;

const VARTIME: bool = true;
type Timing = util::VarTime;
type Scalar0 = Scalar<0, VARTIME>;


fn criterion_benchmark(c: &mut Criterion) {
    let mut rng = rand_xorshift::XorShiftRng::from_seed([
        0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
        0xbc, 0xe5,
    ]);

    // Pairings
    {
        let g = G1Affine::generator();
        let h = G2Affine::generator();
        c.bench_function("full pairing", move |b| {
            b.iter(|| pairing::<VARTIME>(black_box(&g), black_box(&h)))
        });
        c.bench_function("G2 preparation for pairing", move |b| {
            b.iter(|| G2Prepared::from(h))
        });
        let prep = G2Prepared::from(h);
        c.bench_function("miller loop for pairing", move |b| {
            b.iter(|| multi_miller_loop(&[(&g, &prep)]))
        });
        let prep = G2Prepared::from(h);
        let r = multi_miller_loop(&[(&g, &prep)]);
        c.bench_function("final exponentiation for pairing", move |b| {
            b.iter(|| r.final_exponentiation::<VARTIME>())
        });
    }
    // G1Affine
    {
        let name = "G1Affine";
        let a = G1Affine::<VARTIME>::generator();
        let s = Scalar::from_raw([1, 2, 3, 4]);
        let compressed = [0u8; 48];
        let uncompressed = [0u8; 96];
        c.bench_function(&format!("{} check on curve", name), move |b| {
            b.iter(|| black_box(a).is_on_curve())
        });
        c.bench_function(&format!("{} check equality", name), move |b| {
            b.iter(|| black_box(a) == black_box(a))
        });
        c.bench_function(&format!("{} scalar multiplication", name), move |b| {
            b.iter(|| black_box(a).mul(black_box(&s)))
        });
        c.bench_function(&format!("{} subgroup check", name), move |b| {
            b.iter(|| black_box(a).is_torsion_free())
        });
        c.bench_function(
            &format!("{} deserialize compressed point", name),
            move |b| b.iter(|| G1Affine::<VARTIME>::from_compressed(black_box(&compressed))),
        );
        c.bench_function(
            &format!("{} deserialize uncompressed point", name),
            move |b| b.iter(|| G1Affine::from_uncompressed(black_box(&uncompressed))),
        );
    }

    // G1Projective
    {
        let name = "G1Projective";
        let a = G1Projective::<VARTIME>::generator();
        let a_affine = G1Affine::generator();
        let s = Scalar::from_raw([1, 2, 3, 4]);

        const N: usize = 10000;
        let v = vec![G1Projective::<VARTIME>::generator(); N];
        let mut q = vec![G1Affine::<VARTIME>::identity(); N];

        c.bench_function(&format!("{} check on curve", name), move |b| {
            b.iter(|| black_box(a).is_on_curve())
        });
        c.bench_function(&format!("{} check equality", name), move |b| {
            b.iter(|| black_box(a) == black_box(a))
        });
        c.bench_function(&format!("{} to affine", name), move |b| {
            b.iter(|| G1Affine::from(black_box(a)))
        });
        c.bench_function(&format!("{} doubling", name), move |b| {
            b.iter(|| black_box(a).double())
        });
        c.bench_function(&format!("{} addition", name), move |b| {
            b.iter(|| black_box(a).add(&a))
        });
        c.bench_function(&format!("{} mixed addition", name), move |b| {
            b.iter(|| black_box(a).add_mixed(&a_affine))
        });
        c.bench_function(&format!("{} scalar multiplication", name), move |b| {
            b.iter(|| black_box(a).mul(black_box(&s)))
        });
        c.bench_function(&format!("{} batch to affine n={}", name, N), move |b| {
            b.iter(|| {
                G1Projective::batch_normalize(black_box(&v), black_box(&mut q));
                black_box(&q)[0]
            })
        });
    }

    // G1AProjective
    {
        let name = "G1ProjectiveA";
        let a = G1ProjectiveA::<Timing>::generator();
        let a_affine = G1AffineA::<Timing>::generator();
        let s: Scalar = Scalar::from_raw([1, 2, 3, 4]);
        c.bench_function(&format!("{} doubling", name), move |b| {
            b.iter(|| black_box(a).double())
        });
        c.bench_function(&format!("{} addition", name), move |b| {
            b.iter(|| black_box(a).add(&a))
        });
        c.bench_function(&format!("{} mixed addition", name), move |b| {
            b.iter(|| black_box(a).add_mixed(&a_affine))
        });
    }

    // G1Precompute
    {
        let name = "G1Precompute";
        let a = G1Precompute::<512, Timing>::from(G1ProjectiveA::generator());
        let s = Scalar0::from_raw([1, 2, 3, 4]);
        let s = s.to_bytes();

        c.bench_function(&format!("{} scalar multiplication", name), move |b| {
            b.iter(|| black_box(a).multiply_vartime(black_box(&s)))
        });
    }
    // G1PrecomputeAffine
    {
        let name = "G1PrecomputeAffine";
        let a = G1PrecomputeAffine::from(G1Precompute::<512, Timing>::from(G1ProjectiveA::generator()));
        let s = Scalar0::from_raw([1, 2, 3, 4]);
        let va = [(); 32].map(|()| G1PrecomputeAffine::from(G1Precompute::<512, Timing>::from(G1ProjectiveA::generator().mul(&Scalar::random(&mut rng)))));
        let vs = [(); 32].map(|()| Scalar0::random(&mut rng));

        c.bench_function(&format!("{} scalar multiplication", name), move |b| {
            b.iter(|| black_box(a).multiply_vartime(black_box(&s)))
        });
        c.bench_function(&format!("{} dot product", name), move |b| {
            b.iter(|| G1PrecomputeAffine::dot_product_const::<32, VARTIME>(black_box(&va), black_box(&vs)))
        });

    }

    // G2Affine
    {
        let name = "G2Affine";
        let a = G2Affine::generator();
        let s = Scalar::from_raw([1, 2, 3, 4]);
        let compressed = [0u8; 96];
        let uncompressed = [0u8; 192];
        c.bench_function(&format!("{} check on curve", name), move |b| {
            b.iter(|| black_box(a).is_on_curve())
        });
        c.bench_function(&format!("{} check equality", name), move |b| {
            b.iter(|| black_box(a) == black_box(a))
        });
        c.bench_function(&format!("{} scalar multiplication", name), move |b| {
            b.iter(|| black_box(a).mul::<VARTIME>(black_box(&s)))
        });
        c.bench_function(&format!("{} subgroup check", name), move |b| {
            b.iter(|| black_box(a).is_torsion_free())
        });
        c.bench_function(
            &format!("{} deserialize compressed point", name),
            move |b| b.iter(|| G2Affine::from_compressed(black_box(&compressed))),
        );
        c.bench_function(
            &format!("{} deserialize uncompressed point", name),
            move |b| b.iter(|| G2Affine::from_uncompressed(black_box(&uncompressed))),
        );
    }

    // G2Projective
    {
        let name = "G2Projective";
        let a = G2Projective::generator();
        let a_affine = G2Affine::generator();
        let s = Scalar::from_raw([1, 2, 3, 4]);

        const N: usize = 10000;
        let v = vec![G2Projective::generator(); N];
        let mut q = vec![G2Affine::identity(); N];

        c.bench_function(&format!("{} check on curve", name), move |b| {
            b.iter(|| black_box(a).is_on_curve())
        });
        c.bench_function(&format!("{} check equality", name), move |b| {
            b.iter(|| black_box(a) == black_box(a))
        });
        c.bench_function(&format!("{} to affine", name), move |b| {
            b.iter(|| G2Affine::from(black_box(a)))
        });
        c.bench_function(&format!("{} doubling", name), move |b| {
            b.iter(|| black_box(a).double::<VARTIME>())
        });
        c.bench_function(&format!("{} addition", name), move |b| {
            b.iter(|| black_box(a).add(&a))
        });
        c.bench_function(&format!("{} mixed addition", name), move |b| {
            b.iter(|| black_box(a).add_mixed(&a_affine))
        });
        c.bench_function(&format!("{} scalar multiplication", name), move |b| {
            b.iter(|| black_box(a).mul::<VARTIME>(black_box(&s)))
        });
        c.bench_function(&format!("{} batch to affine n={}", name, N), move |b| {
            b.iter(|| {
                G2Projective::batch_normalize(black_box(&v), black_box(&mut q));
                black_box(&q)[0]
            })
        });
    }

    // Fp
    {
        let name = "Fp";
        let a = Fp::<0, true>::random(&mut rng);

        c.bench_function(&format!("{} sqrt", name), move |b| {
            b.iter(|| black_box(a).sqrt_vartime())
        });
    }
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
