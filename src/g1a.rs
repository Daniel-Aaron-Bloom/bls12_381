use subtle::{Choice, ConstantTimeEq, ConditionallySelectable, ConditionallyNegatable};

use crate::{fp::FpA, util::{FpMag, borrowing_sub, mac, Timing, ConstTime, VarTime, Precompute}, Scalar, scalar};


/// This is an element of $\mathbb{G}_1$ represented in the affine coordinate space.
/// It is ideal to keep elements in this representation to reduce memory usage and
/// improve performance through the use of mixed curve model arithmetic.
///
/// Values of `G1Affine` are guaranteed to be in the $q$-order subgroup unless an
/// "unchecked" API was misused.
#[cfg_attr(docsrs, doc(cfg(feature = "groups")))]
#[derive(Copy, Clone, Debug)]
pub struct G1Affine<T: Timing = ConstTime> {
    pub(crate) x: FpA<FpMag<0>, T>,
    pub(crate) y: FpA<FpMag<0>, T>,
    infinity: T::Choice,
}

impl G1Affine<VarTime> {
    /// Returns the identity of the group: the point at infinity.
    pub const fn const_identity() -> Self {
        G1Affine {
            x: FpA::zero(),
            y: FpA::one(),
            infinity: true,
        }
    }

    /// Negate this point
    pub const fn const_neg(&self) -> Self {
        Self {
            x: self.x,
            y: if self.infinity {
                FpA::one()
            } else {
                self.y.neg()
            },
            infinity: self.infinity,
        }
    }
    /// Convert a G1Projective into an G1Affine
    pub const fn from(p: G1Projective<VarTime>) -> Self {
        if p.is_identity_vartime() {
            return Self::const_identity()
        }

        let zinv = match p.z.invert_vartime() {
            Some(v) => v,
            None => panic!("invert is broken"),
        };
        let x = p.x.mul(&zinv).montgomery_reduce().mag();
        let y = p.y.mul(&zinv).montgomery_reduce().mag();

        G1Affine {
            x,
            y,
            infinity: false,
        }
    }

    /// Returns true if this element is the identity (the point at infinity).
    #[inline]
    pub const fn is_identity_vartime(&self) -> bool {
        self.infinity
    }

    /// Returns true if this point is on the curve. This should always return
    /// true unless an "unchecked" API was used.
    pub const fn is_on_curve_vartime(&self) -> bool {
        if self.infinity {
            return true
        }
        // y^2 - x^3 ?= 4
        let y_2 = self.y.square();
        let x_3 = self.x.square().montgomery_reduce().mul(&self.x);
        y_2.sub(&x_3).montgomery_reduce().eq_vartime(&B.vartime())
    }
}

impl<T: Timing> G1Affine<T> {
    /// Returns the identity of the group: the point at infinity.
    pub fn identity() -> Self {
        G1Affine {
            x: FpA::zero(),
            y: FpA::one(),
            infinity: T::from_bool(true),
        }
    }

    /// Returns a fixed generator of the group. See [`notes::design`](notes/design/index.html#fixed-generators)
    /// for how this generator is chosen.
    pub fn generator() -> Self {
        G1Affine {
            x: FpA::from_raw_unchecked([
                0x5cb3_8790_fd53_0c16,
                0x7817_fc67_9976_fff5,
                0x154f_95c7_143b_a1c1,
                0xf0ae_6acd_f3d0_e747,
                0xedce_6ecc_21db_f440,
                0x1201_7741_9e0b_fb75,
            ]),
            y: FpA::from_raw_unchecked([
                0xbaac_93d5_0ce7_2271,
                0x8c22_631a_7918_fd8e,
                0xdd59_5f13_5707_25ce,
                0x51ac_5829_5040_5194,
                0x0e1c_8c3f_ad00_59c0,
                0x0bbc_3efc_5008_a26a,
            ]),
            infinity: T::from_bool(false),
        }
    }

    /// Adjusts the `T` setting
    #[inline]
    pub fn vartime<T2: Timing>(self) -> G1Affine<T2> {
        G1Affine{
            x: self.x.vartime(),
            y: self.y.vartime(),
            infinity: T2::from_bool(T::to_bool(self.infinity)),
        }
    }

    /// Returns true if this element is the identity (the point at infinity).
    #[inline]
    pub fn is_identity(&self) -> Choice {
        T::to_choice(self.infinity)
    }

    /// Returns true if this point is on the curve. This should always return
    /// true unless an "unchecked" API was used.
    pub fn is_on_curve(&self) -> Choice {
        // y^2 - x^3 ?= 4
        let y_2 = self.y.square();
        let x_3 = self.x.square().montgomery_reduce().mul(&self.x);
        y_2.sub(&x_3).montgomery_reduce().mag().ct_eq(&B.vartime()) | T::to_choice(self.infinity)
    }

    /// Serializes this element into compressed form. See [`notes::serialization`](crate::notes::serialization)
    /// for details about how group elements are serialized.
    pub fn to_compressed(&self) -> [u8; 48] {
        let infinity = T::to_choice(self.infinity);
        // Strictly speaking, self.x is zero already when self.infinity is true, but
        // to guard against implementation mistakes we do not assume this.
        let mut res = FpA::conditional_select(&self.x, &FpA::zero(), infinity).to_bytes();

        // This point is in compressed form, so we set the most significant bit.
        res[0] |= 1u8 << 7;

        // Is this point at infinity? If so, set the second-most significant bit.
        res[0] |= u8::conditional_select(&0u8, &(1u8 << 6), infinity);

        // Is the y-coordinate the lexicographically largest of the two associated with the
        // x-coordinate? If so, set the third-most significant bit so long as this is not
        // the point at infinity.
        res[0] |= u8::conditional_select(
            &0u8,
            &(1u8 << 5),
            (!infinity) & self.y.lexicographically_largest(),
        );

        res
    }
}

const B: FpA = FpA::from_raw_unchecked([
    0xaa27_0000_000c_fff3,
    0x53cc_0032_fc34_000a,
    0x478f_e97a_6b0a_807f,
    0xb1d3_7ebe_e6ba_24d7,
    0x8ec9_733b_bf78_ab2f,
    0x09d6_4551_3d83_de7e,
]);

/// A nontrivial third root of unity in Fp
pub const BETA: FpA = FpA::from_raw_unchecked([
    0x30f1_361b_798a_64e8,
    0xf3b8_ddab_7ece_5a2a,
    0x16a8_ca3a_c615_77f7,
    0xc26a_2ff8_74fd_029b,
    0x3636_b766_6070_1c6e,
    0x051b_a4ab_241b_6160,
]);

const BETA_2: FpA = FpA::from_raw_unchecked([
    0xCD03_C9E4_8671_F071,
    0x5DAB_2246_1FCD_A5D2,
    0x5870_42AF_D385_1B95,
    0x8EB6_0EBE_01BA_CB9E,
    0x03F9_7D6E_83D0_50D2,
    0x18F0_2065_5463_8741,
]);

/// This is an element of $\mathbb{G}_1$ represented in the projective coordinate space.
#[cfg_attr(docsrs, doc(cfg(feature = "groups")))]
#[derive(Copy, Clone, Debug)]
pub struct G1Projective<T: Timing = ConstTime> {
    pub(crate) x: FpA<FpMag<0>, T>,
    pub(crate) y: FpA<FpMag<0>, T>,
    pub(crate) z: FpA<FpMag<0>, T>,
}

macro_rules! mul_by_3b {
    ($a:expr) => {{
        let a = ($a).lsh::<2>(); // 4
        a.double().add(&a) // 12
    }};
}

impl<T: Timing> G1Projective<T> {
    /// Returns the identity of the group: the point at infinity.
    pub const fn identity() -> Self {
        G1Projective {
            x: FpA::zero(),
            y: FpA::one(),
            z: FpA::zero(),
        }
    }

    /// Returns a fixed generator of the group. See [`notes::design`](notes/design/index.html#fixed-generators)
    /// for how this generator is chosen.
    pub const fn generator() -> Self {
        G1Projective {
            x: FpA::from_raw_unchecked([
                0x5cb3_8790_fd53_0c16,
                0x7817_fc67_9976_fff5,
                0x154f_95c7_143b_a1c1,
                0xf0ae_6acd_f3d0_e747,
                0xedce_6ecc_21db_f440,
                0x1201_7741_9e0b_fb75,
            ]),
            y: FpA::from_raw_unchecked([
                0xbaac_93d5_0ce7_2271,
                0x8c22_631a_7918_fd8e,
                0xdd59_5f13_5707_25ce,
                0x51ac_5829_5040_5194,
                0x0e1c_8c3f_ad00_59c0,
                0x0bbc_3efc_5008_a26a,
            ]),
            z: FpA::one(),
        }
    }

    /// Adjusts the `T` setting
    #[inline]
    pub const fn vartime<T2: Timing>(self) -> G1Projective<T2> {
        G1Projective{
            x: self.x.vartime(),
            y: self.y.vartime(),
            z: self.z.vartime(),
        }
    }

    /// Returns true if this element is the identity (the point at infinity).
    #[inline]
    pub fn is_identity(&self) -> Choice {
        self.z.is_zero()
    }

    /// Returns true if this element is the identity (the point at infinity).
    #[inline]
    pub const fn is_identity_vartime(&self) -> bool {
        self.z.is_zero_vartime()
    }

    /// Returns true if the elements are equivalent
    #[inline]
    pub fn eq(self, rhs: &Self) -> Choice {
        // Is (xz, yz, z) equal to (x'z', y'z', z') when converted to affine?

        let x1 = self.x.mul(&rhs.z);
        let x2 = rhs.x.mul(&self.z);

        let y1 = self.y.mul(&rhs.z);
        let y2 = rhs.y.mul(&self.z);

        let self_is_zero = self.z.is_zero();
        let other_is_zero = rhs.z.is_zero();

        (self_is_zero & other_is_zero) // Both point at infinity
            | ((!self_is_zero) & (!other_is_zero) & x1.ct_eq(&x2) & y1.ct_eq(&y2))
        // Neither point at infinity, coordinates are the same
    }

    /// Returns true if the elements are equivalent
    #[inline]
    pub const fn eq_vartime(self, rhs: &Self) -> bool {
        // Is (xz, yz, z) equal to (x'z', y'z', z') when converted to affine?
        match (self.is_identity_vartime(), rhs.is_identity_vartime()) {
            // Both point at infinity
            (true, true) => true,
            // Neither point at infinity, check if coordinates are the same
            (false, false) => {
                let x1 = self.x.mul(&rhs.z);
                let x2 = rhs.x.mul(&self.z);
        
                let y1 = self.y.mul(&rhs.z);
                let y2 = rhs.y.mul(&self.z);
        
                x1.eq_vartime(&x2) && y1.eq_vartime(&y2)
            },
            // One point at infinity
            (_, _) => false,
        }
    }

    /// Negate this point
    #[inline]
    pub const fn neg(self) -> Self {
        G1Projective {
            x: self.x,
            y: self.y.neg(),
            z: self.z,
        }
    }

    /// Computes the doubling of this point.
    pub const fn double(&self) -> Self {
        if T::VAR && self.is_identity_vartime() { return *self }

        // Algorithm 9, https://eprint.iacr.org/2015/1060.pdf
        let t0 = self.y.square().montgomery_reduce();
        let z3 = t0.lsh::<3>();
        let t1 = self.y.mul(&self.z).montgomery_reduce();
        let t2 = self.z.square();
        let t2 = mul_by_3b!(t2.montgomery_reduce());
        let x3 = t2.mul(&z3).montgomery_reduce(); // t2 * z3
        let y3 = t0.add(&t2);
        let z3 = t1.mul(&z3);
        let t1 = t2.double();
        let t2 = t1.add(&t2);
        let t0 = t0.sub(&t2);
        let y3 = t0.mul(&y3).montgomery_reduce(); // t0 * y3
        let y3 = x3.add(&y3);
        let t1 = self.x.mul(&self.y).montgomery_reduce();
        let x3 = t0.mul(&t1);
        let x3 = x3.double();

        G1Projective {
            x: x3.montgomery_reduce().mag(),
            y: y3.mag(),
            z: z3.montgomery_reduce().mag(),
        }
    }

    /// Adds this point to another point.
    pub const fn add(self, rhs: &Self) -> Self {
        // Algorithm 7, https://eprint.iacr.org/2015/1060.pdf

        let t0 = self.x.mul(&rhs.x).montgomery_reduce();
        let t1 = self.y.mul(&rhs.y).montgomery_reduce();
        let t2 = self.z.mul(&rhs.z).montgomery_reduce();
        let t3 = self.x.add(&self.y);
        let t4 = rhs.x.add(&rhs.y);
        let t3 = t3.mul(&t4).montgomery_reduce();
        let t4 = t0.add(&t1);
        let t3 = t3.sub(&t4);
        let t4 = self.y.add(&self.z);
        let x3 = rhs.y.add(&rhs.z);
        let t4 = t4.mul(&x3).montgomery_reduce();
        let x3 = t1.add(&t2);
        let t4 = t4.sub(&x3);
        let x3 = self.x.add(&self.z);
        let y3 = rhs.x.add(&rhs.z);
        let x3 = x3.mul(&y3).montgomery_reduce();
        let y3 = t0.add(&t2);
        let y3 = x3.sub(&y3);
        let x3 = t0.double();
        let t0 = x3.add(&t0);
        let t2 = mul_by_3b!(t2);
        let z3 = t1.add(&t2);
        let t1 = t1.sub(&t2);
        let y3 = mul_by_3b!(y3);
        let x3 = t4.mul(&y3); // t4 * y3
        let t2 = t3.mul(&t1); // t3 * t1
        let x3 = t2.sub(&x3);
        let y3 = y3.mul(&t0); // y3 * t0
        let t1 = t1.mul(&z3); // t1 * z3
        let y3 = t1.add(&y3);
        let t0 = t0.mul(&t3); // t0 * t3
        let z3 = z3.mul(&t4); // z3 * t4
        let z3 = z3.add(&t0);

        G1Projective {
            x: x3.montgomery_reduce().mag(),
            y: y3.montgomery_reduce().mag(),
            z: z3.montgomery_reduce().mag(),
        }
    }
    
    /// Adds this point to another point in the affine model.
    const fn add_mixed_helper<T2: Timing>(&self, rhs: &G1Affine<T2>) -> Self {
        // Algorithm 8, https://eprint.iacr.org/2015/1060.pdf

        let rhs_x = rhs.x.vartime();
        let rhs_y = rhs.y.vartime();

        let t0 = self.x.mul(&rhs_x).montgomery_reduce();
        let t1 = self.y.mul(&rhs_y).montgomery_reduce();
        let t3 = rhs_x.add(&rhs_y);
        let t4 = self.x.add(&self.y);
        let t3 = t3.mul(&t4).montgomery_reduce();
        let t4 = t0.add(&t1);
        let t3 = t3.sub(&t4);
        let t4 = rhs_y.mul(&self.z).montgomery_reduce();
        let t4 = t4.add(&self.y);
        let y3 = rhs_x.mul(&self.z).montgomery_reduce();
        let y3 = y3.add(&self.x);
        let x3 = t0.double();
        let t0 = x3.add(&t0);
        let t2 = mul_by_3b!(self.z);
        let z3 = t1.add(&t2);
        let t1 = t1.sub(&t2);
        let y3 = mul_by_3b!(y3);
        let x3 = t4.mul(&y3); // t4 * y3
        let t2 = t3.mul(&t1); // t3 * t1
        let x3 = t2.sub(&x3);
        let y3 = y3.mul(&t0); // y3 * t0
        let t1 = t1.mul(&z3); // t1 * z3
        let y3 = t1.add(&y3);
        let t0 = t0.mul(&t3); // t0 * t3
        let z3 = z3.mul(&t4); // z3 * t4
        let z3 = z3.add(&t0);

        G1Projective {
            x: x3.montgomery_reduce().mag(),
            y: y3.montgomery_reduce().mag(),
            z: z3.montgomery_reduce().mag(),
        }
    }

    /// Adds this point to another point in the affine model.
    pub fn add_mixed(&self, rhs: &G1Affine<T>) -> Self {
        match T::VAR {
            true if T::to_bool(rhs.infinity) => *self,
            true => self.add_mixed_helper(rhs),
            false => G1Projective::conditional_select(&self.add_mixed_helper(rhs), self, rhs.is_identity())
        }
    }
    /// Adds this point to another point in the affine model.
    pub const fn add_mixed_vartime(&self, rhs: &G1Affine<VarTime>) -> Self {
        if rhs.is_identity_vartime() {
            *self
        } else {
            self.add_mixed_helper(&rhs)
        }
    }

    /// Multiplies this point by a scalar.
    #[inline]
    pub fn mul(self, other: &Scalar<0, false>) -> G1Projective<T> {
        G1Precompute::<8, _>::from(self).multiply(&other.to_bytes())
    }

    /// Returns true if this point is on the curve. This should always return
    /// true unless an "unchecked" API was used.
    pub fn is_on_curve(&self) -> Choice {
        // Y^2 Z = X^3 + b Z^3
        let lhs = self.y.square().montgomery_reduce().mul(&self.z).montgomery_reduce();
        let x_3 = self.x.square().montgomery_reduce().mul(&self.x);
        let bz_3 = self.z.square().montgomery_reduce().mul(&self.z).montgomery_reduce().mul(&B.vartime());
        let rhs = x_3.add(&bz_3).montgomery_reduce();
        lhs.ct_eq(&rhs) | self.z.is_zero()
    }

    /// Returns true if this point is on the curve. This should always return
    /// true unless an "unchecked" API was used.
    pub const fn is_on_curve_vartime(&self) -> bool {
        if self.z.is_zero_vartime() {
            return true
        }

        // Y^2 Z = X^3 + b Z^3
        let lhs = self.y.square().montgomery_reduce().mul(&self.z).montgomery_reduce();
        let x_3 = self.x.square().montgomery_reduce().mul(&self.x);
        let bz_3 = self.z.square().montgomery_reduce().mul(&self.z).montgomery_reduce().mul(&B.vartime());
        let rhs = x_3.add(&bz_3).montgomery_reduce();
        lhs.eq_vartime(&rhs)
    }

    /// Converts a batch of `G1Projective` elements into `G1Affine` elements. This
    /// function will panic if `p.len() != q.len()`.
    pub fn batch_normalize(p: &[Self], q: &mut [G1Affine<T>]) {
        assert_eq!(p.len(), q.len());

        let mut acc = FpA::one();
        for (p, q) in p.iter().zip(q.iter_mut()) {
            // We use the `x` field of `G1Affine` to store the product
            // of previous z-coordinates seen.
            q.x = acc;

            // We will end up skipping all identities in p
            let v = acc.mul(&p.z).montgomery_reduce().mag();
            acc = FpA::conditional_select(&v, &acc, p.is_identity());
        }

        // This is the inverse, as all z-coordinates are nonzero and the ones
        // that are not are skipped.
        let mut acc = acc.invert().unwrap();

        for (p, q) in p.iter().rev().zip(q.iter_mut().rev()) {
            let skip = p.is_identity();

            // Compute tmp = 1/z
            let tmp = acc.mul(&q.x).montgomery_reduce();

            // Cancel out z-coordinate in denominator of `acc`
            let v = acc.mul(&p.z).montgomery_reduce().mag();
            acc = FpA::conditional_select(&v, &acc, skip);

            // Set the coordinates to the correct value
            q.x = tmp.mul(&p.x).montgomery_reduce().mag();
            q.y = tmp.mul(&p.y).montgomery_reduce().mag();
            q.infinity = T::from_bool(false);

            *q = G1Affine::conditional_select(q, &G1Affine::identity(), skip);
        }
    }
    
    /// Converts a batch of `G1Projective` elements into `G1Affine` elements. This
    /// function will panic if `p.len() != q.len()`.
    pub const fn batch_normalize_vartime<const N: usize>(p: &[Self; N]) -> [G1Affine<VarTime>; N] {
        let mut q = [G1Affine::const_identity(); N];

        let mut acc = FpA::one();
        {let mut i = 0;
        while i < N {
            let p = p[i].vartime();
            // We use the `x` field of `G1Affine` to store the product
            // of previous z-coordinates seen.
            q[i].x = acc;
            // We will end up skipping all identities in p
            if !p.is_identity_vartime() {
                acc = acc.mul(&p.z).montgomery_reduce().mag();
            }
            i += 1;
        }}

        // This is the inverse, as all z-coordinates are nonzero and the ones
        // that are not are skipped.
        let mut acc = match acc.invert_vartime() {
            Some(v) => v,
            None => panic!("invert failed"),
        };

        {
            let mut i = N;
            while i > 0 {
                i -= 1;
                let p = p[i].vartime();
                let skip = p.is_identity_vartime();
                // Compute tmp = 1/z
                let tmp = acc.mul(&q[i].x).montgomery_reduce();

                // Cancel out z-coordinate in denominator of `acc`
                if !skip {
                    acc = acc.mul(&p.z).montgomery_reduce().mag();

                    // Set the coordinates to the correct value
                    q[i].x = tmp.mul(&p.x).montgomery_reduce().mag();
                    q[i].y = tmp.mul(&p.y).montgomery_reduce().mag();
                    q[i].infinity = false;
                } else {
                    q[i] = G1Affine::const_identity();
                }
            }
        }

        q
    }
}

#[inline]
const fn mul_short(a: &[u64; 4], b: &[u64; 4]) -> [u64; 8] {
    // Schoolbook multiplication
    let (r0, carry) = mac(0, a[0], b[0], 0);
    let (r1, carry) = mac(0, a[0], b[1], carry);
    let (r2, carry) = mac(0, a[0], b[2], carry);
    let r3 = carry;

    let (r1, carry) = mac(r1, a[1], b[0], 0);
    let (r2, carry) = mac(r2, a[1], b[1], carry);
    let (r3, carry) = mac(r3, a[1], b[2], carry);
    let r4 = carry;

    let (r2, carry) = mac(r2, a[2], b[0], 0);
    let (r3, carry) = mac(r3, a[2], b[1], carry);
    let (r4, carry) = mac(r4, a[2], b[2], carry);
    let r5 = carry;

    let (r3, carry) = mac(r3, a[3], b[0], 0);
    let (r4, carry) = mac(r4, a[3], b[1], carry);
    let (r5, carry) = mac(r5, a[3], b[2], carry);
    let r6 = carry;

    [r0, r1, r2, r3, r4, r5, r6, 0]
}

type Flag = i16;

const fn glv_recoding(k: &[u8; 32]) -> (Flag, [u8; 32], Flag, [u8; 32]) {
    const V: [[u64; 4]; 2] = [
        [0x63f6_e522_f6cf_ee2f, 0x7c6b_ecf1_e01f_aadd, 1, 0],
        [0x0000_0000_ffff_ffff, 0xac45_a401_0001_a402, 0, 0],
    ];

    let t: [u64; 4] = [
        le_bytes_to_u64!(k[0..]),
        le_bytes_to_u64!(k[8..]),
        le_bytes_to_u64!(k[16..]),
        le_bytes_to_u64!(k[24..]),
    ];

    /* Multiply b2 by v[0] and round. */
    let b2 = mul_short(&t, &V[0]);
    let b2h = [b2[4] + (b2[3] >> 63), b2[5], b2[6], b2[7]];

    let b1 = mul_short(&b2h, &V[1]);
    let b1l = [b1[0], b1[1], b1[2], b1[3]];
    let (b1l, s1) = scalar::sub_c(&t, &b1l);
    let minus_k1: Scalar = (&Scalar::from_raw([!b1l[0], !b1l[1], !b1l[2], !b1l[3]])).add(&Scalar::one());

    let k1 = Scalar::from_raw(b1l);
    let k1 = Scalar::select(k1, minus_k1, s1);
    let k2: Scalar = Scalar::from_raw(b2h);

    // k2 is always positive for this curve.
    (-(s1 as Flag), k1.to_bytes(), 0, k2.to_bytes())
}

const fn regular_recoding(w: u32, len: usize, sc: [u8; 32]) -> [Flag; 129] {
    let mut naf = [0 as Flag; 129];

    // Joux-Tunstall regular recoding algorithm for parameterized w.
    let mask = (1 << w) - 1;

    let mut sc = [
        u128::from_le_bytes([sc[0], sc[1], sc[2], sc[3], sc[4], sc[5], sc[6], sc[7], sc[8], sc[9], sc[10], sc[11], sc[12], sc[13], sc[14], sc[15]]),
        u128::from_le_bytes([sc[16], sc[17], sc[18], sc[19], sc[20], sc[21], sc[22], sc[23], sc[24], sc[25], sc[26], sc[27], sc[28], sc[29], sc[30], sc[31]]),
    ];

    let mut i = 0;
    while i  < len - 1 {
        naf[i] = ((sc[0] & mask) as Flag) - (1 << (w - 1));
        sc[0] = ((sc[0] as i128) - naf[i] as i128) as u128;
        // Divide by (w - 1)
        sc[0] = (sc[0] >> (w - 1)) | sc[1] << (u128::BITS - (w - 1));
        sc[1] >>= w - 1;

        i += 1;
    }

    naf[len - 1] = sc[0] as Flag;
    
    naf
}

const fn recode_scalar(w: u32, by: &[u8; 32]) -> (Flag, Flag, u8, u8, [Flag; 129], [Flag; 129]) {
    let (s1, mut k1, s2, mut k2) = glv_recoding(&by);

    let bit1 = k1[0] & 1u8;
    k1[0] |= 1;
    let bit2 = k2[0] & 1u8;
    k2[0] |= 1;

    let len = 2 + (128 - 1) / (w - 1) as usize;
    let naf1 = regular_recoding(w, len, k1);
    let naf2 = regular_recoding(w, len, k2);
    (s1, s2, bit1, bit2, naf1, naf2)
}

#[derive(Debug, Copy, Clone)]
struct ScalarRecode {
    s1: Flag,
    s2: Flag,
    bit1: u8,
    bit2: u8,
    naf1: [Flag; 129],
    naf2: [Flag; 129],
}

impl ScalarRecode {
    const fn new() -> Self {
        Self {
            s1: 0, s2: 0, bit1: 0, bit2: 0, naf1: [0; 129], naf2: [0; 129]
        }
    }

    const fn from<const P: usize, const VARTIME: bool>(s: &Scalar<0, VARTIME>) -> Self
    where FpMag<P>: Precompute {
        let (s1, mut k1, s2, mut k2) = glv_recoding(&s.to_bytes());

        let bit1 = k1[0] & 1u8;
        k1[0] |= 1;
        let bit2 = k2[0] & 1u8;
        k2[0] |= 1;
    
        let len = 2 + (128 - 1) / (FpMag::<P>::W - 1) as usize;
        let naf1 = regular_recoding(FpMag::<P>::W, len, k1);
        let naf2 = regular_recoding(FpMag::<P>::W, len, k2);
        Self{s1, s2, bit1, bit2, naf1, naf2}
    }

}

fn linear_pass<T: Default + ConditionallySelectable>(index: u8, table: &[T]) -> T {
    // Scan table of points to read table[index]
    let mut tmp = table[0];
    for (j, jv) in table.iter().enumerate().skip(1) {
        tmp.conditional_assign(jv, (j as u8).ct_eq(&index));
    }
    tmp
}

/// A `G1Projective` specialized for fast multiplication
#[derive(Copy, Clone, Debug)]
pub struct G1Precompute<const P: usize, T: Timing>
where FpMag<P>: Precompute {
    table: [G1Projective<T>; P],
}

/// A `G1Affine` specialized for fast multiplication
#[derive(Copy, Clone, Debug)]
pub struct G1PrecomputeAffine<const P: usize, T: Timing>
where FpMag<P>: Precompute {
    table: [G1Affine<T>; P],
}

impl<const P: usize, T: Timing> G1Precompute<P, T> 
where FpMag<P>: Precompute {
    /// Build a G1Precompute from a `G1Projective`
    pub const fn from(v: G1Projective<T>) -> Self {
        let mut table = [v; P];
       
        if FpMag::<P>::W > 2 {
            let double_point = v.double();
            let mut prev = v;
            let mut i = 1;
            while i < table.len() {
                prev = prev.add(&double_point);
                table[i] = prev;
                i += 1;
            }
        }

        Self { table }
    }

    /// Multiplies this point by a scalar.
    pub fn multiply(&self, by: &[u8; 32]) -> G1Projective<T> {
        let len = 2 + (128 - 1) / (FpMag::<P>::W - 1) as usize;
        let (s1, s2, bit1, bit2, naf1, naf2) = recode_scalar(FpMag::<P>::W, by);

        let table = &self.table;
        let mut acc = G1Projective::identity();
        let mut i = len;
        while i > 0 {
            i -= 1;
            let mut j = 1;
            while i != len - 1 && j < FpMag::<P>::W {
                acc = acc.double();
                j += 1;
            }
            let sign = naf1[i] >> (Flag::BITS - 1);
            let index = ((naf1[i] ^ sign) - sign) >> 1;
            let t = match T::VAR {
                // Negate point if either k1 or naf1[i] is negative.
                true if sign != s1 => table[index as usize].neg(),
                true => table[index as usize],
                false => {
                    let mut t = linear_pass(index as u8, table);
                    // Negate point if either k1 or naf1[i] is negative.
                    t.conditional_negate(Choice::from(-(sign ^ s1) as u8));
                    t
                }
            };
            acc = acc.add(&t);

            let sign = naf2[i] >> (Flag::BITS - 1);
            let index = ((naf2[i] ^ sign) - sign) >> 1;
            let mut t = match T::VAR {
                // Negate point if either k2 or naf2[i] is negative.
                true if sign != s2 => table[index as usize].neg(),
                true => table[index as usize],
                false => {
                    let mut t = linear_pass(index as u8, table);
                    t.conditional_negate(Choice::from(-(sign ^ s2) as u8));
                    t
                }
            };
            t.x = t.x.mul(&BETA_2.vartime()).montgomery_reduce().mag();
            acc = acc.add(&t);
        }

        // If the subscalars were even, fix result here.
        let t = match T::VAR {
            true if s1 == -1 => table[0].neg(),
            true => table[0],
            false => ConditionallySelectable::conditional_select(
                &table[0],
                &table[0].neg(),
                Choice::from(-s1 as u8),
            ),
        };
        acc = match T::VAR {
            true if bit1 == 1 => acc,
            true => acc.add(&t.neg()),
            false => G1Projective::conditional_select(&acc.add(&t.neg()), &acc, Choice::from(bit1))
        };
        let mut table_0 = table[0];
        table_0.x = table_0.x.mul(&BETA_2.vartime()).montgomery_reduce().mag();
        let t = match T::VAR {
            true if s2 == -1 => table_0.neg(),
            true => table_0,
            false => ConditionallySelectable::conditional_select(
                &table_0,
                &table_0.neg(),
                Choice::from(-s2 as u8),
            ),
        };
        match T::VAR {
            true if bit2 == 1 => acc,
            true => acc.add(&t.neg()),
            false => G1Projective::conditional_select(&acc.add(&t.neg()), &acc, Choice::from(bit2)),
        }
    }

    /// Multiplies this point by a scalar.
    pub const fn multiply_vartime(&self, by: &[u8; 32]) -> G1Projective<T> {
        // let (s1, mut k1, s2, mut k2) = glv_recoding(&by);

        // let bit1 = k1[0] & 1u8;
        // k1[0] |= 1;
        // let bit2 = k2[0] & 1u8;
        // k2[0] |= 1;

        // let len = 2 + (128 - 1) / (FpMag::<P>::W - 1) as usize;
        // let naf1 = regular_recoding(FpMag::<P>::W, len, k1);
        // let naf2 = regular_recoding(FpMag::<P>::W, len, k2);

        let len = 2 + (128 - 1) / (FpMag::<P>::W - 1) as usize;
        let (s1, s2, bit1, bit2, naf1, naf2) = recode_scalar(FpMag::<P>::W, by);

        let table = &self.table;
        let mut acc = G1Projective::identity();
        let mut i = len;
        while i > 0 {
            i -= 1;
            let mut j = 1;
            while i != len - 1 && j < FpMag::<P>::W {
                acc = acc.double();
                j += 1;
            }
            let sign = naf1[i] >> (Flag::BITS - 1);
            let index = ((naf1[i] ^ sign) - sign) >> 1;
            // Negate point if either k1 or naf1[i] is negative.
            let t = if sign != s1 {
                table[index as usize].neg()
            } else {
                table[index as usize]
            };
            acc = acc.add(&t);

            let sign = naf2[i] >> (Flag::BITS - 1);
            let index = ((naf2[i] ^ sign) - sign) >> 1;
            let mut t = if sign != s2 {
                // Negate point if either k2 or naf2[i] is negative.
                table[index as usize].neg()
            } else {
                table[index as usize]
            };
            t.x = t.x.mul(&BETA_2.vartime()).montgomery_reduce().mag();
            acc = acc.add(&t);
        }
        // If the subscalars were even, fix result here.
        if bit1 != 1 {
            if s1 == -1 {
                acc = acc.add(&table[0]);
            } else {
                acc = acc.add(&table[0].neg());
            };
        }
        let mut table_0 = table[0];
        table_0.x = table_0.x.mul(&BETA_2.vartime()).montgomery_reduce().mag();

        match bit2 {
            1 => acc,
            _ if s2 == -1 => acc.add(&table_0),
            _ => acc.add(&table_0.neg()),
        }
    }
}

impl<const P: usize> G1PrecomputeAffine<P, VarTime> 
where FpMag<P>: Precompute {
    /// Build a G1PrecomputeAffine from a `G1Precompute`
    pub const fn from<T: Timing>(v: G1Precompute<P, T>) -> Self {
        Self {
            table: G1Projective::batch_normalize_vartime(&v.table)
        }
    }

    /// Multiplies this point by a scalar.
    pub const fn multiply_vartime<const VARTIME: bool>(&self, s: &Scalar<0, VARTIME>) -> G1Projective<VarTime> {
        let len = 2 + (128 - 1) / (FpMag::<P>::W - 1) as usize;
        let ScalarRecode{s1, s2, bit1, bit2, naf1, naf2} = ScalarRecode::from::<P, VARTIME>(s);

        let table = &self.table;
        let mut acc = G1Projective::identity();
        let mut i = len;
        while i > 0 {
            i -= 1;
            let mut j = 1;
            while i != len - 1 && j < FpMag::<P>::W {
                acc = acc.double();
                j += 1;
            }
            let sign = naf1[i] >> (Flag::BITS - 1);
            let index = ((naf1[i] ^ sign) - sign) >> 1;
            // Negate point if either k1 or naf1[i] is negative.
            let t = if sign != s1 {
                table[index as usize].const_neg()
            } else {
                table[index as usize]
            };
            acc = acc.add_mixed_vartime(&t);

            let sign = naf2[i] >> (Flag::BITS - 1);
            let index = ((naf2[i] ^ sign) - sign) >> 1;
            let mut t = if sign != s2 {
                // Negate point if either k2 or naf2[i] is negative.
                table[index as usize].const_neg()
            } else {
                table[index as usize]
            };
            t.x = t.x.mul(&BETA_2.vartime()).montgomery_reduce().mag();
            acc = acc.add_mixed_vartime(&t);
        }
        // If the subscalars were even, fix result here.
        if bit1 != 1 {
            if s1 == -1 {
                acc = acc.add_mixed_vartime(&table[0]);
            } else {
                acc = acc.add_mixed_vartime(&table[0].const_neg());
            };
        }
        let mut table_0 = table[0];
        table_0.x = table_0.x.mul(&BETA_2.vartime()).montgomery_reduce().mag();

        match bit2 {
            1 => acc,
            _ if s2 == -1 => acc.add_mixed_vartime(&table_0),
            _ => acc.add_mixed_vartime(&table_0.const_neg()),
        }
    }

    /// Multiplies and sums a series of points by a series of corresponding scalars.
    pub const fn dot_product_const<const S: usize, const VARTIME: bool>(v: &[Self], s: &[Scalar<0, VARTIME>]) -> G1Projective<VarTime> {
        
        let len = 2 + (128 - 1) / (FpMag::<P>::W - 1) as usize;
        let s = {
            let mut recodes = [ScalarRecode::new(); S];
            let mut s_i = 0;
            while s_i < s.len() {
                recodes[s_i] = ScalarRecode::from::<P, VARTIME>(&s[s_i]);
                s_i += 1;
            }
            recodes
        };
         

        let mut acc = G1Projective::identity();
        let mut i = len;
        while i > 0 {
            i -= 1;
            {
                let mut j = 1;
                while i != len - 1 && j < FpMag::<P>::W {
                    acc = acc.double();
                    j += 1;
                }
            }

            let mut s_i = 0;
            while s_i < s.len() {
                let table = &v[s_i].table;
                let &ScalarRecode{s1, s2, ref naf1, ref naf2, ..} = &s[s_i];
                s_i += 1;

                let sign = naf1[i] >> (Flag::BITS - 1);
                let index = ((naf1[i] ^ sign) - sign) >> 1;
                // Negate point if either k1 or naf1[i] is negative.
                let t = if sign != s1 {
                    table[index as usize].const_neg()
                } else {
                    table[index as usize]
                };
                acc = acc.add_mixed_vartime(&t);

                let sign = naf2[i] >> (Flag::BITS - 1);
                let index = ((naf2[i] ^ sign) - sign) >> 1;
                let mut t = if sign != s2 {
                    // Negate point if either k2 or naf2[i] is negative.
                    table[index as usize].const_neg()
                } else {
                    table[index as usize]
                };
                t.x = t.x.mul(&BETA_2.vartime()).montgomery_reduce().mag();

                acc = acc.add_mixed_vartime(&t);
            }
        }

        let mut s_i = 0;
        while s_i < s.len() {
            let table = &v[s_i].table;
            let &ScalarRecode{s1, s2, bit1, bit2, ..} = &s[s_i];
            s_i += 1;

            // If the subscalars were even, fix result here.
            if bit1 != 1 {
                if s1 == -1 {
                    acc = acc.add_mixed_vartime(&table[0]);
                } else {
                    acc = acc.add_mixed_vartime(&table[0].const_neg());
                };
            }
            let mut table_0 = table[0];
            table_0.x = table_0.x.mul(&BETA_2.vartime()).montgomery_reduce().mag();

            acc = match bit2 {
                1 => acc,
                _ if s2 == -1 => acc.add_mixed_vartime(&table_0),
                _ => acc.add_mixed_vartime(&table_0.const_neg()),
            };
        }
        acc
    }


    #[cfg(feature = "alloc")]
    /// Multiplies and sums a series of points by a series of corresponding scalars.
    pub fn dot_product<const VARTIME: bool>(v: &[Self], s: &[Scalar<0, VARTIME>]) -> G1Projective<VarTime> {
        use alloc::vec::Vec;

        assert!(v.len() >= s.len());
        
        let len = 2 + (128 - 1) / (FpMag::<P>::W - 1) as usize;
        let s = s.iter()
            .map(|s| ScalarRecode::from::<P, VARTIME>(&s))
            .collect::<Vec<_>>();
         

        let mut acc = G1Projective::identity();
        let mut i = len;
        while i > 0 {
            i -= 1;
            {
                let mut j = 1;
                while i != len - 1 && j < FpMag::<P>::W {
                    acc = acc.double();
                    j += 1;
                }
            }

            let mut s_i = 0;
            while s_i < s.len() {
                let table = &v[s_i].table;
                let &ScalarRecode{s1, s2, ref naf1, ref naf2, ..} = &s[s_i];
                s_i += 1;

                let sign = naf1[i] >> (Flag::BITS - 1);
                let index = ((naf1[i] ^ sign) - sign) >> 1;
                // Negate point if either k1 or naf1[i] is negative.
                let t = if sign != s1 {
                    table[index as usize].const_neg()
                } else {
                    table[index as usize]
                };
                acc = acc.add_mixed_vartime(&t);

                let sign = naf2[i] >> (Flag::BITS - 1);
                let index = ((naf2[i] ^ sign) - sign) >> 1;
                let mut t = if sign != s2 {
                    // Negate point if either k2 or naf2[i] is negative.
                    table[index as usize].const_neg()
                } else {
                    table[index as usize]
                };
                t.x = t.x.mul(&BETA_2.vartime()).montgomery_reduce().mag();

                acc = acc.add_mixed_vartime(&t);
            }
        }

        let mut s_i = 0;
        while s_i < s.len() {
            let table = &v[s_i].table;
            let &ScalarRecode{s1, s2, bit1, bit2, ..} = &s[s_i];
            s_i += 1;

            // If the subscalars were even, fix result here.
            if bit1 != 1 {
                if s1 == -1 {
                    acc = acc.add_mixed_vartime(&table[0]);
                } else {
                    acc = acc.add_mixed_vartime(&table[0].const_neg());
                };
            }
            let mut table_0 = table[0];
            table_0.x = table_0.x.mul(&BETA_2.vartime()).montgomery_reduce().mag();

            acc = match bit2 {
                1 => acc,
                _ if s2 == -1 => acc.add_mixed_vartime(&table_0),
                _ => acc.add_mixed_vartime(&table_0.const_neg()),
            };
        }
        acc
    }

}

mod ops;

#[cfg(test)]
mod test;
