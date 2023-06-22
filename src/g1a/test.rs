use super::*;
use ff::Field;
use rand_core::SeedableRng;

#[test]
fn test_doubling() {
    let mut rng = rand_xorshift::XorShiftRng::from_seed([
        0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
        0xbc, 0xe5,
    ]);

    {
        let tmp: G1Projective = G1Projective::identity().double();
        assert!(bool::from(tmp.is_identity()));
        assert!(bool::from(tmp.is_on_curve()));
    }
    for _ in 0..100_000 {
        let tmp: G1Projective = G1Projective{
            x: FpA::random(&mut rng),
            y: FpA::random(&mut rng),
            z: FpA::zero(),
        }.double();
        assert!(bool::from(tmp.is_identity()));
        assert!(bool::from(tmp.is_on_curve()));
    }
    {
        let tmp: G1Projective = G1Projective::generator().double();
        assert!(!bool::from(tmp.is_identity()));
        assert!(bool::from(tmp.is_on_curve()));

        assert_eq!(
            <G1Affine as From<_>>::from(tmp),
            G1Affine {
                x: FpA::from_raw_unchecked([
                    0x53e9_78ce_58a9_ba3c,
                    0x3ea0_583c_4f3d_65f9,
                    0x4d20_bb47_f001_2960,
                    0xa54c_664a_e5b2_b5d9,
                    0x26b5_52a3_9d7e_b21f,
                    0x0008_895d_26e6_8785,
                ]),
                y: FpA::from_raw_unchecked([
                    0x7011_0b32_9829_3940,
                    0xda33_c539_3f1f_6afc,
                    0xb86e_dfd1_6a5a_a785,
                    0xaec6_d1c9_e7b1_c895,
                    0x25cf_c2b5_22d1_1720,
                    0x0636_1c83_f8d0_9b15,
                ]),
                infinity: Choice::from(0u8)
            }
        );
    }
}

#[test]
fn test_projective_addition() {

    {
        let a: G1Projective = G1Projective::identity();
        let b: G1Projective = G1Projective::identity();
        let c = a + b;
        assert!(bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
    }
    {
        let a: G1Projective = G1Projective::generator();
        let b: G1Projective = G1Projective::generator();
        let c = a + b;
        assert!(bool::from(!c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
    }
    {
        let a: G1Projective = G1Projective::generator();
        let b: G1Projective = G1Projective::generator();
        let c = a - b;
        assert!(bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
    }
    {
        let a: G1Projective = G1Projective::identity();
        let mut b = G1Projective::generator();
        {
            let z = FpA::from_raw_unchecked([
                0xba7a_fa1f_9a6f_e250,
                0xfa0f_5b59_5eaf_e731,
                0x3bdc_4776_94c3_06e7,
                0x2149_be4b_3949_fa24,
                0x64aa_6e06_49b2_078c,
                0x12b1_08ac_3364_3c3e,
            ]);

            b = G1Projective {
                x: b.x.mul(&z).montgomery_reduce().mag(),
                y: b.y.mul(&z).montgomery_reduce().mag(),
                z,
            };
        }
        let c = a + b;
        assert!(!bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
        assert!(c == G1Projective::generator());
    }
    
    {
        let a: G1Projective = G1Projective::identity();
        let mut b = G1Projective::generator();
        {
            let z = FpA::from_raw_unchecked([
                0xba7a_fa1f_9a6f_e250,
                0xfa0f_5b59_5eaf_e731,
                0x3bdc_4776_94c3_06e7,
                0x2149_be4b_3949_fa24,
                0x64aa_6e06_49b2_078c,
                0x12b1_08ac_3364_3c3e,
            ]);

            b = G1Projective {
                x: b.x.mul(&z).montgomery_reduce().mag(),
                y: b.y.mul(&z).montgomery_reduce().mag(),
                z,
            };
        }
        let c = b + a;
        assert!(!bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
        assert!(c == G1Projective::generator());
    }
    {
        let a: G1Projective = G1Projective::generator().double().double(); // 4P
        let b = G1Projective::generator().double(); // 2P
        let c = a + b;

        let mut d = G1Projective::generator();
        for _ in 0..5 {
            d += G1Projective::generator();
        }
        assert!(!bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
        assert!(!bool::from(d.is_identity()));
        assert!(bool::from(d.is_on_curve()));
        assert_eq!(c, d);
    }

    // Degenerate case
    {
        let beta: FpA = FpA::from_raw_unchecked([
            0xcd03_c9e4_8671_f071,
            0x5dab_2246_1fcd_a5d2,
            0x5870_42af_d385_1b95,
            0x8eb6_0ebe_01ba_cb9e,
            0x03f9_7d6e_83d0_50d2,
            0x18f0_2065_5463_8741,
        ]);
        let beta = beta.square().montgomery_reduce();
        let a = G1Projective::generator().double().double();
        let b = G1Projective {
            x: a.x.mul(&beta).montgomery_reduce().mag(),
            y: a.y.neg(),
            z: a.z,
        };
        assert!(bool::from(a.is_on_curve()));
        assert!(bool::from(b.is_on_curve()));

        let c = a + b;
        assert_eq!(
            <G1Affine as From<_>>::from(c),
            <G1Affine as From<_>>::from(G1Projective {
                x: FpA::from_raw_unchecked([
                    0x29e1_e987_ef68_f2d0,
                    0xc5f3_ec53_1db0_3233,
                    0xacd6_c4b6_ca19_730f,
                    0x18ad_9e82_7bc2_bab7,
                    0x46e3_b2c5_785c_c7a9,
                    0x07e5_71d4_2d22_ddd6,
                ]),
                y: FpA::from_raw_unchecked([
                    0x94d1_17a7_e5a5_39e7,
                    0x8e17_ef67_3d4b_5d22,
                    0x9d74_6aaf_508a_33ea,
                    0x8c6d_883d_2516_c9a2,
                    0x0bc3_b8d5_fb04_47f7,
                    0x07bf_a4c7_210f_4f44,
                ]),
                z: FpA::one()
            })
        );
        assert!(!bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
    }
}

#[test]
fn test_mixed_addition() {
    {
        let a: G1Affine = G1Affine::identity();
        let b: G1Projective = G1Projective::identity();
        let c = b.add_mixed(&a);
        assert!(bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
    }
    {
        let a: G1Affine = G1Affine::identity();
        let mut b: G1Projective = G1Projective::generator();
        {
            let z = FpA::from_raw_unchecked([
                0xba7a_fa1f_9a6f_e250,
                0xfa0f_5b59_5eaf_e731,
                0x3bdc_4776_94c3_06e7,
                0x2149_be4b_3949_fa24,
                0x64aa_6e06_49b2_078c,
                0x12b1_08ac_3364_3c3e,
            ]);

            b = G1Projective {
                x: b.x.mul(&z).montgomery_reduce().mag(),
                y: b.y.mul(&z).montgomery_reduce().mag(),
                z,
            };
        }
        let c = b.add_mixed(&a);
        assert!(!bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
        assert!(c == G1Projective::generator());
    }
    {
        let a: G1Affine = G1Affine::identity();
        let mut b = G1Projective::generator();
        {
            let z = FpA::from_raw_unchecked([
                0xba7a_fa1f_9a6f_e250,
                0xfa0f_5b59_5eaf_e731,
                0x3bdc_4776_94c3_06e7,
                0x2149_be4b_3949_fa24,
                0x64aa_6e06_49b2_078c,
                0x12b1_08ac_3364_3c3e,
            ]);

            b = G1Projective {
                x: b.x.mul(&z).montgomery_reduce().mag(),
                y: b.y.mul(&z).montgomery_reduce().mag(),
                z,
            };
        }
        let c = b.add_mixed(&a);
        assert!(!bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
        assert!(c == G1Projective::generator());
    }
    {
        let a: G1Projective = G1Projective::generator().double().double(); // 4P
        let b = G1Projective::generator().double(); // 2P
        let c = a + b;

        let mut d = G1Projective::generator();
        for _ in 0..5 {
            d = d.add_mixed(&G1Affine::generator());
        }
        assert!(!bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
        assert!(!bool::from(d.is_identity()));
        assert!(bool::from(d.is_on_curve()));
        assert_eq!(c, d);
    }

    // Degenerate case
    {
        let beta: FpA = FpA::from_raw_unchecked([
            0xcd03_c9e4_8671_f071,
            0x5dab_2246_1fcd_a5d2,
            0x5870_42af_d385_1b95,
            0x8eb6_0ebe_01ba_cb9e,
            0x03f9_7d6e_83d0_50d2,
            0x18f0_2065_5463_8741,
        ]);
        let beta = beta.square().montgomery_reduce();
        let a = G1Projective::generator().double().double();
        let b = G1Projective {
            x: a.x.mul(&beta).montgomery_reduce().mag(),
            y: a.y.neg(),
            z: a.z,
        };
        let a = G1Affine::from(a.vartime());
        assert!(bool::from(a.is_on_curve()));
        assert!(bool::from(b.is_on_curve()));

        let c = b.add_mixed(&a.vartime());
        assert_eq!(
            G1Affine::from(c.vartime()),
            G1Affine::from(G1Projective {
                x: FpA::from_raw_unchecked([
                    0x29e1_e987_ef68_f2d0,
                    0xc5f3_ec53_1db0_3233,
                    0xacd6_c4b6_ca19_730f,
                    0x18ad_9e82_7bc2_bab7,
                    0x46e3_b2c5_785c_c7a9,
                    0x07e5_71d4_2d22_ddd6,
                ]),
                y: FpA::from_raw_unchecked([
                    0x94d1_17a7_e5a5_39e7,
                    0x8e17_ef67_3d4b_5d22,
                    0x9d74_6aaf_508a_33ea,
                    0x8c6d_883d_2516_c9a2,
                    0x0bc3_b8d5_fb04_47f7,
                    0x07bf_a4c7_210f_4f44,
                ]),
                z: FpA::one()
            })
        );
        assert!(!bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
    }
}

#[test]
fn test_addition() {
    let mut rng = rand_xorshift::XorShiftRng::from_seed([
        0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
        0xbc, 0xe5,
    ]);

    let mut acc: G1Projective = G1Projective::identity();
    let mut acc0 = G1Projective::identity();
    let mut acc1 = G1Projective::identity();
    for _ in 0..10_000 {
        let s1 = Scalar::random(&mut rng);
        let s2 = Scalar::random(&mut rng);
        let a: G1Projective = G1Projective::generator().mul(&s1);
        let b: G1Projective = G1Projective::generator().mul(&s2);

        let aa: G1Affine = G1Affine::from(a.vartime()).vartime();
        let mut ab: G1Affine = G1Affine::from(b.vartime()).vartime();
        ab.x = ab.x.mul(&BETA_2.vartime()).montgomery_reduce().mag();

        acc = acc.add_mixed_vartime(&aa.vartime());
        acc0 = acc0.add_mixed_vartime(&aa.vartime());
        let acct = acc0.add(&acc1);
        assert!(acc.eq_vartime(&acct));

        acc = acc.add_mixed_vartime(&ab.vartime());
        acc1 = acc1.add_mixed_vartime(&ab.vartime());
        let acct = acc0.add(&acc1);
        assert!(acc.eq_vartime(&acct));
    }
}

#[test]
fn test_projective_scalar_multiplication() {
    let g: G1Projective = G1Projective::generator();
    let a = Scalar::from_raw([
        0x2b56_8297_a56d_a71c,
        0xd8c3_9ecb_0ef3_75d1,
        0x435c_38da_67bf_bf96,
        0x8088_a050_26b6_59b2,
    ]);
    let b = Scalar::from_raw([
        0x785f_dd9b_26ef_8b85,
        0xc997_f258_3769_5c18,
        0x4c8d_bc39_e7b7_56c1,
        0x70d9_b6cc_6d87_df20,
    ]);
    let c = a * b;

    assert_eq!(g.mul(&a).mul(&b) , g.mul(&c));
}

#[test]
fn test_g1_precompute_affine_dot_product() {
    type Scalar0 = Scalar<0, true>;
    let mut rng = rand_xorshift::XorShiftRng::from_seed([
        0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
        0xbc, 0xe5,
    ]);

    let vg = [
        G1PrecomputeAffine::from(G1Precompute::<512, VarTime>::from(G1Projective::generator())),
    ];

    let va = [Scalar0::from_raw([
        0x2b56_8297_a56d_a71c,
        0xd8c3_9ecb_0ef3_75d1,
        0x435c_38da_67bf_bf96,
        0x8088_a050_26b6_59b2,
    ])];

    assert_eq!(G1PrecomputeAffine::dot_product_const::<1, true>(&vg, &va), vg[0].multiply_vartime(&va[0]));

    let g = G1Projective::generator();
    let vg = [
        G1PrecomputeAffine::from(G1Precompute::<512, VarTime>::from(g.mul(&Scalar::random(&mut rng)))),
        G1PrecomputeAffine::from(G1Precompute::<512, VarTime>::from(g.mul(&Scalar::random(&mut rng)))),
        G1PrecomputeAffine::from(G1Precompute::<512, VarTime>::from(g.mul(&Scalar::random(&mut rng)))),
        G1PrecomputeAffine::from(G1Precompute::<512, VarTime>::from(g.mul(&Scalar::random(&mut rng)))),
    ];

    let a = g.mul(&Scalar::random(&mut rng));
    let b = g.mul(&Scalar::random(&mut rng));

    assert_eq!(a.double().add(&b.double()), a.add(&b).double());

    let va = [
        Scalar0::random(&mut rng),
        Scalar0::random(&mut rng),
        Scalar0::random(&mut rng),
        Scalar0::random(&mut rng),
    ];

    let a = G1PrecomputeAffine::dot_product_const::<4, true>(&vg, &va);
    let b = vg[0].multiply_vartime(&va[0])
        .add(&vg[1].multiply_vartime(&va[1]))
        .add(&vg[2].multiply_vartime(&va[2]))
        .add(&vg[3].multiply_vartime(&va[3]));
    assert_eq!(a, b);
}