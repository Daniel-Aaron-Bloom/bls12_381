//! This module provides an implementation of the $\mathbb{G}_1$ group of BLS12-381.

use core::borrow::Borrow;
use core::fmt;
use core::iter::Sum;
use core::ops::{Add, Mul, MulAssign, Neg, Sub};
use group::{
    prime::{PrimeCurve, PrimeCurveAffine, PrimeGroup},
    Curve, Group, GroupEncoding, UncompressedEncoding,
};
use rand_core::RngCore;
use subtle::{Choice, ConditionallyNegatable, ConditionallySelectable, ConstantTimeEq, CtOption};

#[cfg(feature = "alloc")]
use group::WnafGroup;

use crate::fp::Fp;
use crate::util::{mac, sbb, MulOp, DoubleOp, MontOp, borrowing_sub, SquareOp, Ops};
use crate::Scalar;

/// This is an element of $\mathbb{G}_1$ represented in the affine coordinate space.
/// It is ideal to keep elements in this representation to reduce memory usage and
/// improve performance through the use of mixed curve model arithmetic.
///
/// Values of `G1Affine` are guaranteed to be in the $q$-order subgroup unless an
/// "unchecked" API was misused.
#[cfg_attr(docsrs, doc(cfg(feature = "groups")))]
#[derive(Copy, Clone, Debug)]
pub struct G1Affine<const VARTIME: bool = false> {
    pub(crate) x: Fp<0, VARTIME>,
    pub(crate) y: Fp<0, VARTIME>,
    infinity: Choice,
}

impl Default for G1Affine {
    fn default() -> G1Affine {
        G1Affine::identity()
    }
}

#[cfg(feature = "zeroize")]
impl zeroize::DefaultIsZeroes for G1Affine {}

impl<const VARTIME: bool> fmt::Display for G1Affine<VARTIME> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<'a, const VARTIME: bool> From<&'a G1Projective<VARTIME>> for G1Affine<VARTIME> {
    fn from(p: &'a G1Projective<VARTIME>) -> G1Affine<VARTIME> {
        let zinv = p.z.invert().unwrap_or(Fp::zero());
        let x = p.x * zinv;
        let y = p.y * zinv;

        let tmp = G1Affine {
            x,
            y,
            infinity: Choice::from(0u8),
        };

        G1Affine::conditional_select(&tmp, &G1Affine::identity(), zinv.is_zero())
    }
}

impl<const VARTIME: bool> From<G1Projective<VARTIME>> for G1Affine<VARTIME> {
    fn from(p: G1Projective<VARTIME>) -> G1Affine<VARTIME> {
        G1Affine::from(&p)
    }
}

impl<const VARTIME: bool> ConstantTimeEq for G1Affine<VARTIME> {
    fn ct_eq(&self, other: &Self) -> Choice {
        // The only cases in which two points are equal are
        // 1. infinity is set on both
        // 2. infinity is not set on both, and their coordinates are equal

        (self.infinity & other.infinity)
            | ((!self.infinity)
                & (!other.infinity)
                & self.x.ct_eq(&other.x)
                & self.y.ct_eq(&other.y))
    }
}

impl<const VARTIME: bool> ConditionallySelectable for G1Affine<VARTIME> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        G1Affine {
            x: Fp::conditional_select(&a.x, &b.x, choice),
            y: Fp::conditional_select(&a.y, &b.y, choice),
            infinity: Choice::conditional_select(&a.infinity, &b.infinity, choice),
        }
    }
}

impl<const VARTIME: bool> Eq for G1Affine<VARTIME> {}
impl<const VARTIME: bool> PartialEq for G1Affine<VARTIME> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match VARTIME {
            true => self.x == other.x && self.y == other.y && self.infinity.unwrap_u8() == other.infinity.unwrap_u8(),
            false => bool::from(self.ct_eq(other)),
        }
    }
}

impl<'a, const VARTIME: bool> Neg for &'a G1Affine<VARTIME> {
    type Output = G1Affine<VARTIME>;

    #[inline]
    fn neg(self) -> G1Affine<VARTIME> {
        G1Affine {
            x: self.x,
            y: Fp::conditional_select(&-self.y, &Fp::one(), self.infinity),
            infinity: self.infinity,
        }
    }
}

impl<const VARTIME: bool> Neg for G1Affine<VARTIME> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        -&self
    }
}

impl<'a, 'b, const VARTIME: bool> Add<&'b G1Projective<VARTIME>> for &'a G1Affine<VARTIME> {
    type Output = G1Projective<VARTIME>;

    #[inline]
    fn add(self, rhs: &'b G1Projective<VARTIME>) -> G1Projective<VARTIME> {
        rhs.add_mixed(self)
    }
}

impl<'a, 'b, const VARTIME: bool> Add<&'b G1Affine<VARTIME>> for &'a G1Projective<VARTIME> {
    type Output = G1Projective<VARTIME>;

    #[inline]
    fn add(self, rhs: &'b G1Affine<VARTIME>) -> G1Projective<VARTIME> {
        self.add_mixed(rhs)
    }
}

impl<'a, 'b, const VARTIME: bool> Sub<&'b G1Projective<VARTIME>> for &'a G1Affine<VARTIME> {
    type Output = G1Projective<VARTIME>;

    #[inline]
    fn sub(self, rhs: &'b G1Projective<VARTIME>) -> G1Projective<VARTIME> {
        self + (-rhs)
    }
}

impl<'a, 'b, const VARTIME: bool> Sub<&'b G1Affine<VARTIME>> for &'a G1Projective<VARTIME> {
    type Output = G1Projective<VARTIME>;

    #[inline]
    fn sub(self, rhs: &'b G1Affine<VARTIME>) -> G1Projective<VARTIME> {
        self + (-rhs)
    }
}

impl<T, const VARTIME: bool> Sum<T> for G1Projective<VARTIME>
where
    T: Borrow<G1Projective<VARTIME>>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::identity(), |acc, item| acc + item.borrow())
    }
}

impl_binops_additive!{
    {const VARTIME: bool}
    {}
    {G1Projective<VARTIME>} {G1Affine<VARTIME>}
}
impl_binops_additive_output!{
    {const VARTIME: bool}
    {}
    {G1Affine<VARTIME>}
    {G1Projective<VARTIME>}
}

const B: Fp = Fp::from_raw_unchecked([
    0xaa27_0000_000c_fff3,
    0x53cc_0032_fc34_000a,
    0x478f_e97a_6b0a_807f,
    0xb1d3_7ebe_e6ba_24d7,
    0x8ec9_733b_bf78_ab2f,
    0x09d6_4551_3d83_de7e,
]);

impl<const VARTIME: bool> G1Affine<VARTIME> {
    /// Returns the identity of the group: the point at infinity.
    pub fn identity() -> Self {
        G1Affine {
            x: Fp::zero(),
            y: Fp::one(),
            infinity: Choice::from(1u8),
        }
    }

    /// Returns a fixed generator of the group. See [`notes::design`](notes/design/index.html#fixed-generators)
    /// for how this generator is chosen.
    pub fn generator() -> Self {
        G1Affine {
            x: Fp::from_raw_unchecked([
                0x5cb3_8790_fd53_0c16,
                0x7817_fc67_9976_fff5,
                0x154f_95c7_143b_a1c1,
                0xf0ae_6acd_f3d0_e747,
                0xedce_6ecc_21db_f440,
                0x1201_7741_9e0b_fb75,
            ]),
            y: Fp::from_raw_unchecked([
                0xbaac_93d5_0ce7_2271,
                0x8c22_631a_7918_fd8e,
                0xdd59_5f13_5707_25ce,
                0x51ac_5829_5040_5194,
                0x0e1c_8c3f_ad00_59c0,
                0x0bbc_3efc_5008_a26a,
            ]),
            infinity: Choice::from(0u8),
        }
    }

    /// Adjusts the `VARTIME` setting
    #[inline]
    pub const fn vartime<const VARTIME2: bool>(self) -> G1Affine<VARTIME2> {
        G1Affine{
            x: self.x.vartime(),
            y: self.y.vartime(),
            infinity: self.infinity,
        }
    }

    /// Returns true if this element is the identity (the point at infinity).
    #[inline]
    pub fn is_identity(&self) -> Choice {
        self.infinity
    }

    /// Returns true if this element is the identity (the point at infinity).
    #[inline]
    pub fn is_identity_vartime(&self) -> bool {
        self.infinity.into()
    }

    /// Serializes this element into compressed form. See [`notes::serialization`](crate::notes::serialization)
    /// for details about how group elements are serialized.
    pub fn to_compressed(&self) -> [u8; 48] {
        // Strictly speaking, self.x is zero already when self.infinity is true, but
        // to guard against implementation mistakes we do not assume this.
        let mut res = Fp::conditional_select(&self.x, &Fp::zero(), self.infinity).to_bytes();

        // This point is in compressed form, so we set the most significant bit.
        res[0] |= 1u8 << 7;

        // Is this point at infinity? If so, set the second-most significant bit.
        res[0] |= u8::conditional_select(&0u8, &(1u8 << 6), self.infinity);

        // Is the y-coordinate the lexicographically largest of the two associated with the
        // x-coordinate? If so, set the third-most significant bit so long as this is not
        // the point at infinity.
        res[0] |= u8::conditional_select(
            &0u8,
            &(1u8 << 5),
            (!self.infinity) & self.y.lexicographically_largest(),
        );

        res
    }

    /// Multiplies this point by a scalar.
    #[inline]
    pub fn mul(self, other: &Scalar<0, VARTIME>) -> G1Projective<VARTIME> {
        G1Projective::from(self).mul(other)
    }

    /// Returns true if this point is free of an $h$-torsion component, and so it
    /// exists within the $q$-order subgroup $\mathbb{G}_1$. This should always return true
    /// unless an "unchecked" API was used.
    pub fn is_torsion_free(&self) -> Choice {
        // Algorithm from Section 6 of https://eprint.iacr.org/2021/1130
        // Updated proof of correctness in https://eprint.iacr.org/2022/352
        //
        // Check that endomorphism_p(P) == -[x^2] P

        let minus_x_squared_times_p = G1Projective::from(self).mul_by_x().mul_by_x().neg();
        let endomorphism_p = endomorphism(self);
        minus_x_squared_times_p.ct_eq(&G1Projective::from(endomorphism_p))
    }

    /// Returns true if this point is on the curve. This should always return
    /// true unless an "unchecked" API was used.
    pub fn is_on_curve(&self) -> Choice {
        // y^2 - x^3 ?= 4
        let y_2 = SquareOp::square(&self.y);
        let x_3 = MulOp::mul(&MontOp::montgomery_reduce(&SquareOp::square(&self.x)), &self.x);
        Ops::sub(&y_2, &x_3).montgomery_reduce_full().ct_eq(&B.vartime::<VARTIME>()) | self.infinity
    }
}

impl G1Affine {

    /// Serializes this element into uncompressed form. See [`notes::serialization`](crate::notes::serialization)
    /// for details about how group elements are serialized.
    pub fn to_uncompressed(&self) -> [u8; 96] {
        let mut res = [0; 96];

        res[0..48].copy_from_slice(
            &Fp::conditional_select(&self.x, &Fp::zero(), self.infinity).to_bytes()[..],
        );
        res[48..96].copy_from_slice(
            &Fp::conditional_select(&self.y, &Fp::zero(), self.infinity).to_bytes()[..],
        );

        // Is this point at infinity? If so, set the second-most significant bit.
        res[0] |= u8::conditional_select(&0u8, &(1u8 << 6), self.infinity);

        res
    }

    /// Attempts to deserialize an uncompressed element. See [`notes::serialization`](crate::notes::serialization)
    /// for details about how group elements are serialized.
    pub fn from_uncompressed(bytes: &[u8; 96]) -> CtOption<Self> {
        Self::from_uncompressed_unchecked(bytes)
            .and_then(|p| CtOption::new(p, p.is_on_curve() & p.is_torsion_free()))
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is on the curve and not checking if it is in the correct subgroup.
    /// **This is dangerous to call unless you trust the bytes you are reading; otherwise,
    /// API invariants may be broken.** Please consider using `from_uncompressed()` instead.
    pub fn from_uncompressed_unchecked(bytes: &[u8; 96]) -> CtOption<Self> {
        // Obtain the three flags from the start of the byte sequence
        let compression_flag_set = Choice::from((bytes[0] >> 7) & 1);
        let infinity_flag_set = Choice::from((bytes[0] >> 6) & 1);
        let sort_flag_set = Choice::from((bytes[0] >> 5) & 1);

        // Attempt to obtain the x-coordinate
        let x = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[0..48]);

            // Mask away the flag bits
            tmp[0] &= 0b0001_1111;

            Fp::from_bytes(&tmp)
        };

        // Attempt to obtain the y-coordinate
        let y = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[48..96]);

            Fp::from_bytes(&tmp)
        };

        x.and_then(|x| {
            y.and_then(|y| {
                // Create a point representing this value
                let p = G1Affine::conditional_select(
                    &G1Affine {
                        x,
                        y,
                        infinity: infinity_flag_set,
                    },
                    &G1Affine::identity(),
                    infinity_flag_set,
                );

                CtOption::new(
                    p,
                    // If the infinity flag is set, the x and y coordinates should have been zero.
                    ((!infinity_flag_set) | (infinity_flag_set & x.is_zero() & y.is_zero())) &
                    // The compression flag should not have been set, as this is an uncompressed element
                    (!compression_flag_set) &
                    // The sort flag should not have been set, as this is an uncompressed element
                    (!sort_flag_set),
                )
            })
        })
    }

    /// Attempts to deserialize a compressed element. See [`notes::serialization`](crate::notes::serialization)
    /// for details about how group elements are serialized.
    pub fn from_compressed(bytes: &[u8; 48]) -> CtOption<Self> {
        // We already know the point is on the curve because this is established
        // by the y-coordinate recovery procedure in from_compressed_unchecked().

        Self::from_compressed_unchecked(bytes).and_then(|p| CtOption::new(p, p.is_torsion_free()))
    }

    /// Attempts to deserialize an uncompressed element, not checking if the
    /// element is in the correct subgroup.
    /// **This is dangerous to call unless you trust the bytes you are reading; otherwise,
    /// API invariants may be broken.** Please consider using `from_compressed()` instead.
    pub fn from_compressed_unchecked(bytes: &[u8; 48]) -> CtOption<Self> {
        // Obtain the three flags from the start of the byte sequence
        let compression_flag_set = Choice::from((bytes[0] >> 7) & 1);
        let infinity_flag_set = Choice::from((bytes[0] >> 6) & 1);
        let sort_flag_set = Choice::from((bytes[0] >> 5) & 1);

        // Attempt to obtain the x-coordinate
        let x = {
            let mut tmp = [0; 48];
            tmp.copy_from_slice(&bytes[0..48]);

            // Mask away the flag bits
            tmp[0] &= 0b0001_1111;

            Fp::from_bytes(&tmp)
        };

        x.and_then(|x| {
            // If the infinity flag is set, return the value assuming
            // the x-coordinate is zero and the sort bit is not set.
            //
            // Otherwise, return a recovered point (assuming the correct
            // y-coordinate can be found) so long as the infinity flag
            // was not set.
            CtOption::new(
                G1Affine::identity(),
                infinity_flag_set & // Infinity flag should be set
                compression_flag_set & // Compression flag should be set
                (!sort_flag_set) & // Sort flag should not be set
                x.is_zero(), // The x-coordinate should be zero
            )
            .or_else(|| {
                // Recover a y-coordinate given x by y = sqrt(x^3 + 4)
                ((x.square() * x) + B).sqrt().and_then(|y| {
                    // Switch to the correct y-coordinate if necessary.
                    let y = Fp::conditional_select(
                        &y,
                        &-y,
                        y.lexicographically_largest() ^ sort_flag_set,
                    );

                    CtOption::new(
                        G1Affine {
                            x,
                            y,
                            infinity: infinity_flag_set,
                        },
                        (!infinity_flag_set) & // Infinity flag should not be set
                        compression_flag_set, // Compression flag should be set
                    )
                })
            })
        })
    }
}

/// A nontrivial third root of unity in Fp
pub const BETA: Fp = Fp::from_raw_unchecked([
    0x30f1_361b_798a_64e8,
    0xf3b8_ddab_7ece_5a2a,
    0x16a8_ca3a_c615_77f7,
    0xc26a_2ff8_74fd_029b,
    0x3636_b766_6070_1c6e,
    0x051b_a4ab_241b_6160,
]);

const BETA_2: Fp = Fp::from_raw_unchecked([
    0xCD03_C9E4_8671_F071,
    0x5DAB_2246_1FCD_A5D2,
    0x5870_42AF_D385_1B95,
    0x8EB6_0EBE_01BA_CB9E,
    0x03F9_7D6E_83D0_50D2,
    0x18F0_2065_5463_8741,
]);

// The recoding width that determines the length and size of precomputation table.
// Tested values are in 3..8.
const G1_WIDTH: i32 = 5;
const G1_LEN: usize = 2 + (128 - 1) / (G1_WIDTH - 1) as usize;

#[inline]
const fn sub_short(a: &[u64; 4], b: &[u64; 4]) -> ([u64; 4], bool) {
    let (d0, borrow) = borrowing_sub(a[0], b[0], false);
    let (d1, borrow) = borrowing_sub(a[1], b[1], borrow);
    let (d2, borrow) = borrowing_sub(a[2], b[2], borrow);
    let (d3, borrow) = borrowing_sub(a[3], b[3], borrow);
    ([d0, d1, d2, d3], borrow)
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

const fn glv_recoding<const VARTIME: bool>(k: &[u8; 32]) -> (i8, [u8; 32], i8, [u8; 32]) {
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
    let (b1l, s1) = sub_short(&t, &b1l);
    let minus_k1: Scalar = (&Scalar::from_raw([!b1l[0], !b1l[1], !b1l[2], !b1l[3]])).add(&Scalar::one());

    let k1 = Scalar::from_raw(b1l);
    let k1 = Scalar::select(k1, minus_k1, s1);
    let k2: Scalar = Scalar::from_raw(b2h);

    // k2 is always positive for this curve.
    (-(s1 as i8), k1.to_bytes(), 0, k2.to_bytes())
}

const fn regular_recoding(w: i32, len: usize, mut sc: [u8; 32]) -> [i8; 129] {
    let mut naf = [0 as i8; 129];

    // Joux-Tunstall regular recoding algorithm for parameterized w.
    let mask = (1 << w) - 1;

    let mut i = 0;
    while i  < len - 1 {
        naf[i] = ((sc[0] & mask) as i8) - (1 << (w - 1));
        sc[0] = ((sc[0] as i8) - naf[i]) as u8;
        // Divide by (w - 1)
        let mut j = 0;
        while j < 31 {
            sc[j] = (sc[j] >> (w - 1)) | sc[j + 1] << (8 - (w - 1));
            j += 1;
        }
        sc[31] >>= w - 1;
        i += 1;
    }
    naf[len - 1] = sc[0] as i8;
    naf
}

fn endomorphism<const VARTIME: bool>(p: &G1Affine<VARTIME>) -> G1Affine<VARTIME> {
    // Endomorphism of the points on the curve.
    // endomorphism_p(x,y) = (BETA * x, y)
    // where BETA is a non-trivial cubic root of unity in Fq.
    let mut res = *p;
    res.x *= BETA.vartime::<VARTIME>();
    res
}

/// This is an element of $\mathbb{G}_1$ represented in the projective coordinate space.
#[cfg_attr(docsrs, doc(cfg(feature = "groups")))]
#[derive(Copy, Clone, Debug)]
pub struct G1Projective<const VARTIME: bool = false> {
    pub(crate) x: Fp<0, VARTIME>,
    pub(crate) y: Fp<0, VARTIME>,
    pub(crate) z: Fp<0, VARTIME>,
}

impl<const VARTIME: bool> Default for G1Projective<VARTIME> {
    fn default() -> Self {
        G1Projective::identity()
    }
}

#[cfg(feature = "zeroize")]
impl<const VARTIME: bool> zeroize::DefaultIsZeroes for G1Projective<VARTIME> {}

impl<const VARTIME: bool> fmt::Display for G1Projective<VARTIME> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<'a, const VARTIME: bool> From<&'a G1Affine<VARTIME>> for G1Projective<VARTIME> {
    fn from(p: &'a G1Affine<VARTIME>) -> Self {
        G1Projective {
            x: p.x,
            y: p.y,
            z: Fp::conditional_select(&Fp::one(), &Fp::zero(), p.infinity),
        }
    }
}

impl<const VARTIME: bool> From<G1Affine<VARTIME>> for G1Projective<VARTIME> {
    fn from(p: G1Affine<VARTIME>) -> Self {
        G1Projective::from(&p)
    }
}

impl<const VARTIME: bool> ConstantTimeEq for G1Projective<VARTIME> {
    fn ct_eq(&self, other: &Self) -> Choice {
        // Is (xz, yz, z) equal to (x'z', y'z', z') when converted to affine?

        let x1 = self.x * other.z;
        let x2 = other.x * self.z;

        let y1 = self.y * other.z;
        let y2 = other.y * self.z;

        let self_is_zero = self.z.is_zero();
        let other_is_zero = other.z.is_zero();

        (self_is_zero & other_is_zero) // Both point at infinity
            | ((!self_is_zero) & (!other_is_zero) & x1.ct_eq(&x2) & y1.ct_eq(&y2))
        // Neither point at infinity, coordinates are the same
    }
}

impl<const VARTIME: bool> ConditionallySelectable for G1Projective<VARTIME> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        G1Projective {
            x: Fp::conditional_select(&a.x, &b.x, choice),
            y: Fp::conditional_select(&a.y, &b.y, choice),
            z: Fp::conditional_select(&a.z, &b.z, choice),
        }
    }
}

impl<const VARTIME: bool> Eq for G1Projective<VARTIME> {}
impl<const VARTIME: bool> PartialEq for G1Projective<VARTIME> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match VARTIME {
            true => self.x == other.x && self.y == other.y && self.z == other.z,
            false => bool::from(self.ct_eq(other)),
        }
    }
}

impl<'a, const VARTIME: bool> Neg for &'a G1Projective<VARTIME> {
    type Output = G1Projective<VARTIME>;

    #[inline]
    fn neg(self) -> G1Projective<VARTIME> {
        G1Projective {
            x: self.x,
            y: -self.y,
            z: self.z,
        }
    }
}

impl<const VARTIME: bool> Neg for G1Projective<VARTIME> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        -&self
    }
}

impl<'a, 'b, const VARTIME: bool> Add<&'b G1Projective<VARTIME>> for &'a G1Projective<VARTIME> {
    type Output = G1Projective<VARTIME>;

    #[inline]
    fn add(self, rhs: &'b G1Projective<VARTIME>) -> Self::Output {
        self.add(rhs)
    }
}

impl<'a, 'b, const VARTIME: bool> Sub<&'b G1Projective<VARTIME>> for &'a G1Projective<VARTIME> {
    type Output = G1Projective<VARTIME>;

    #[inline]
    fn sub(self, rhs: &'b G1Projective<VARTIME>) -> Self::Output {
        self + (-rhs)
    }
}

impl<'a, 'b, const VARTIME: bool> Mul<&'b Scalar<0, VARTIME>> for &'a G1Projective<VARTIME> {
    type Output = G1Projective<VARTIME>;

    fn mul(self, other: &'b Scalar<0, VARTIME>) -> Self::Output {
        self.multiply(&other.to_bytes())
    }
}

impl<'a, 'b, const VARTIME: bool> Mul<&'b G1Projective<VARTIME>> for &'a Scalar<0, VARTIME> {
    type Output = G1Projective<VARTIME>;

    #[inline]
    fn mul(self, rhs: &'b G1Projective<VARTIME>) -> Self::Output {
        rhs * self
    }
}

impl<'a, 'b, const VARTIME: bool> Mul<&'b Scalar<0, VARTIME>> for &'a G1Affine<VARTIME> {
    type Output = G1Projective<VARTIME>;

    fn mul(self, other: &'b Scalar<0, VARTIME>) -> Self::Output {
        G1Projective::from(self).multiply(&other.to_bytes())
    }
}

impl<'a, 'b, const VARTIME: bool> Mul<&'b G1Affine<VARTIME>> for &'a Scalar<0, VARTIME> {
    type Output = G1Projective<VARTIME>;

    #[inline]
    fn mul(self, rhs: &'b G1Affine<VARTIME>) -> Self::Output {
        rhs * self
    }
}

impl_binops_additive!{
    {const VARTIME: bool}
    {}
    {G1Projective<VARTIME>}
    {G1Projective<VARTIME>}
}
impl_binops_multiplicative!{
    {const VARTIME: bool}
    {}
    {G1Projective<VARTIME>}
    {Scalar<0, VARTIME>}
}
impl_binops_multiplicative_mixed!{
    {const VARTIME: bool}
    {}
    {G1Affine<VARTIME>} {Scalar<0, VARTIME>} {G1Projective<VARTIME>}
}
impl_binops_multiplicative_mixed!{
    {const VARTIME: bool}
    {}
    {Scalar<0, VARTIME>} {G1Affine<VARTIME>} {G1Projective<VARTIME>}
}
impl_binops_multiplicative_mixed!{
    {const VARTIME: bool}
    {}
    {Scalar<0, VARTIME>} {G1Projective<VARTIME>} {G1Projective<VARTIME>}
}

#[inline(always)]
fn mul_by_3b<const VARTIME: bool>(a: Fp<0, VARTIME>) -> Fp<0, VARTIME> {
    let a = a.double(); // 2
    let a = a.double(); // 4
    a.double() + a // 12
}

macro_rules! mul_by_3b {
    ($a:expr) => {{
        let a = DoubleOp::<1>::double(&$a); // 4
        Ops::add(&DoubleOp::<0>::double(&a), &a) // 12
    }};
}

impl<const VARTIME: bool> G1Projective<VARTIME> {
    /// Returns the identity of the group: the point at infinity.
    pub fn identity() -> Self {
        G1Projective {
            x: Fp::zero(),
            y: Fp::one(),
            z: Fp::zero(),
        }
    }

    /// Returns a fixed generator of the group. See [`notes::design`](notes/design/index.html#fixed-generators)
    /// for how this generator is chosen.
    pub fn generator() -> Self {
        G1Projective {
            x: Fp::from_raw_unchecked([
                0x5cb3_8790_fd53_0c16,
                0x7817_fc67_9976_fff5,
                0x154f_95c7_143b_a1c1,
                0xf0ae_6acd_f3d0_e747,
                0xedce_6ecc_21db_f440,
                0x1201_7741_9e0b_fb75,
            ]),
            y: Fp::from_raw_unchecked([
                0xbaac_93d5_0ce7_2271,
                0x8c22_631a_7918_fd8e,
                0xdd59_5f13_5707_25ce,
                0x51ac_5829_5040_5194,
                0x0e1c_8c3f_ad00_59c0,
                0x0bbc_3efc_5008_a26a,
            ]),
            z: Fp::one(),
        }
    }

    /// Adjusts the `VARTIME` setting
    #[inline]
    pub const fn vartime<const VARTIME2: bool>(self) -> G1Projective<VARTIME2> {
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

    fn double_helper(&self) -> Self {
        // Algorithm 9, https://eprint.iacr.org/2015/1060.pdf
        let t0 = MontOp::montgomery_reduce(&SquareOp::square(&self.y)).reduce_full();
        let z3 = DoubleOp::<2>::double(&t0);
        let t1 = MontOp::montgomery_reduce(&MulOp::mul(&self.y, &self.z));
        let t2 = SquareOp::square(&self.z);
        let t2 = MontOp::montgomery_reduce(&mul_by_3b!(t2)).reduce_full();
        let x3 = MontOp::montgomery_reduce(&MulOp::mul(&t2, &z3)); // t2 * z3
        let y3 = Ops::add(&t0, &t2);
        let z3 = MulOp::mul(&t1, &z3);
        let t1 = DoubleOp::<0>::double(&t2);
        let t2 = Ops::add(&t1, &t2);
        let t0 = Ops::sub(&t0, &t2);
        let y3 = MontOp::montgomery_reduce(&MulOp::mul(&t0, &y3)); // t0 * y3
        let y3 = Ops::add(&x3, &y3);
        let t1 = MontOp::montgomery_reduce(&MulOp::mul(&self.x, &self.y));
        let x3 = MulOp::mul(&t0, &t1);
        let x3 = DoubleOp::<0>::double(&x3);

        G1Projective {
            x: x3.montgomery_reduce_full(),
            y: y3.reduce_full(),
            z: z3.montgomery_reduce_full(),
        }
    }

    /// Computes the doubling of this point.
    pub fn double(&self) -> Self {
        match VARTIME {
            true if self.is_identity_vartime() => G1Projective::identity(),
            true => self.double_helper(),
            false => {
                G1Projective::conditional_select(&self.double_helper(), self, self.is_identity())
            }
        }
    }

    /// Adds this point to another point.
    pub fn add(&self, rhs: &Self) -> Self {
        // Algorithm 7, https://eprint.iacr.org/2015/1060.pdf

        let t0 = MontOp::montgomery_reduce(&MulOp::mul(&self.x, &rhs.x));
        let t1 = MontOp::montgomery_reduce(&MulOp::mul(&self.y, &rhs.y));
        let t2 = MontOp::montgomery_reduce(&MulOp::mul(&self.z, &rhs.z));
        let t3 = Ops::add(&self.x, &self.y);
        let t4 = Ops::add(&rhs.x, &rhs.y);
        let t3 = MontOp::montgomery_reduce(&MulOp::mul(&t3, &t4));
        let t4 = Ops::add(&t0, &t1);
        let t3 = Ops::sub(&t3, &t4).reduce_full();
        let t4 = Ops::add(&self.y, &self.z);
        let x3 = Ops::add(&rhs.y, &rhs.z);
        let t4 = MontOp::montgomery_reduce(&MulOp::mul(&t4, &x3));
        let x3 = Ops::add(&t1, &t2);
        let t4 = Ops::sub(&t4, &x3).reduce_full();
        let x3 = Ops::add(&self.x, &self.z);
        let y3 = Ops::add(&rhs.x, &rhs.z);
        let x3 = MontOp::montgomery_reduce(&MulOp::mul(&x3, &y3));
        let y3 = Ops::add(&t0, &t2);
        let y3 = Ops::sub(&x3, &y3).reduce_full();
        let x3 = DoubleOp::<0>::double(&t0);
        let t0 = Ops::add(&x3, &t0);
        let t2 = mul_by_3b(t2.reduce_full());
        let z3 = Ops::add(&t1, &t2);
        let t1 = Ops::sub(&t1, &t2).reduce_full();
        let y3 = mul_by_3b(y3.reduce_full());
        let x3 = MulOp::mul(&t4, &y3); // t4 * y3
        let t2 = MulOp::mul(&t3, &t1); // t3 * t1
        let x3 = Ops::sub(&t2, &x3);
        let y3 = MulOp::mul(&y3, &t0); // y3 * t0
        let t1 = MulOp::mul(&t1, &z3); // t1 * z3
        let y3 = Ops::add(&t1, &y3);
        let t0 = MulOp::mul(&t0, &t3); // t0 * t3
        let z3 = MulOp::mul(&z3, &t4); // z3 * t4
        let z3 = Ops::add(&z3, &t0);

        G1Projective {
            x: x3.montgomery_reduce_full(),
            y: y3.montgomery_reduce_full(),
            z: z3.montgomery_reduce_full(),
        }
    }
    
    /// Adds this point to another point in the affine model.
    fn add_mixed_helper(&self, rhs: &G1Affine<VARTIME>) -> Self {
        // Algorithm 8, https://eprint.iacr.org/2015/1060.pdf

        let t0 = MontOp::montgomery_reduce(&MulOp::mul(&self.x, &rhs.x));
        let t1 = MontOp::montgomery_reduce(&MulOp::mul(&self.y, &rhs.y));
        let t3 = Ops::add(&rhs.x, &rhs.y);
        let t4 = Ops::add(&self.x, &self.y);
        let t3 = MontOp::montgomery_reduce(&MulOp::mul(&t3, &t4));
        let t4 = Ops::add(&t0, &t1);
        let t3 = Ops::sub(&t3, &t4);
        let t4 = MontOp::montgomery_reduce(&MulOp::mul(&rhs.y, &self.z));
        let t4 = Ops::add(&t4, &self.y);
        let y3 = MontOp::montgomery_reduce(&MulOp::mul(&rhs.x, &self.z));
        let y3 = Ops::add(&y3, &self.x);
        let x3 = DoubleOp::<0>::double(&t0);
        let t0 = Ops::add(&x3, &t0);
        let t2 = mul_by_3b::<VARTIME>(self.z);
        let z3 = Ops::add(&t1, &t2);
        let t1 = Ops::sub(&t1, &t2);
        let y3 = mul_by_3b::<VARTIME>(y3.reduce_full());
        let x3 = MulOp::mul(&t4, &y3); // t4 * y3
        let t2 = MulOp::mul(&t3, &t1); // t3 * t1
        let x3 = Ops::sub(&t2, &x3);
        let y3 = MulOp::mul(&y3, &t0); // y3 * t0
        let t1 = MulOp::mul(&t1, &z3); // t1 * z3
        let y3 = Ops::add(&t1, &y3);
        let t0 = MulOp::mul(&t0, &t3); // t0 * t3
        let z3 = MulOp::mul(&z3, &t4); // z3 * t4
        let z3 = Ops::add(&z3, &t0);

        G1Projective {
            x: x3.montgomery_reduce_full(),
            y: y3.montgomery_reduce_full(),
            z: z3.montgomery_reduce_full(),
        }
    }

    /// Adds this point to another point in the affine model.
    pub fn add_mixed(&self, rhs: &G1Affine<VARTIME>) -> Self {
        match VARTIME {
            true if rhs.is_identity_vartime() => *self,
            true => self.add_mixed_helper(rhs),
            false => G1Projective::conditional_select(&self.add_mixed_helper(rhs), self, rhs.is_identity())
        }
    }

    /// Multiplies this point by a scalar.
    #[inline]
    pub fn mul(self, other: &Scalar<0, VARTIME>) -> Self {
        self.multiply(&other.to_bytes())
    }

    fn precompute(&self) -> [Self; 1 << (G1_WIDTH - 2)] {
        // Size of precomputation table is 2^(w-2).
        let mut proj_table = [*self; 1 << (G1_WIDTH - 2)];
        if G1_WIDTH > 2 {
            let double_point = self.double();
            let mut prev = *self;
            for i in proj_table.iter_mut().skip(1) {
                prev += double_point;
                *i = prev;
            }
        }
        proj_table
    }

    fn linear_pass<T: Default + ConditionallySelectable>(index: u8, table: &[T]) -> T {
        // Scan table of points to read table[index]
        let mut tmp = table[0];
        for (j, jv) in table.iter().enumerate().skip(1) {
            tmp.conditional_assign(jv, (j as u8).ct_eq(&index));
        }
        tmp
    }

    fn multiply(&self, by: &[u8; 32]) -> Self {
        let mut acc = G1Projective::identity();

        // Length of recoding is ceil(scalar bitlength, w - 1).
        let len = 2 + (128 - 1) / (G1_WIDTH - 1) as usize;

        // Allocate longest possible vector, recode scalar and precompute table.
        let (s1, mut k1, s2, mut k2) = glv_recoding::<VARTIME>(&by);
        let mut table = self.precompute();

        let bit1 = k1[0] & 1u8;
        k1[0] |= 1;
        let bit2 = k2[0] & 1u8;
        k2[0] |= 1;

        let naf1 = regular_recoding(G1_WIDTH, G1_LEN, k1);
        let naf2 = regular_recoding(G1_WIDTH, G1_LEN, k2);

        for i in (0..G1_LEN).rev() {
            for _ in 1..G1_WIDTH {
                acc = acc.double();
            }
            let sign = naf1[i] >> 7;
            let index = ((naf1[i] ^ sign) - sign) >> 1;
            let t = match VARTIME {
                // Negate point if either k1 or naf1[i] is negative.
                true if sign != s1 => -table[index as usize],
                true => table[index as usize],
                false => {
                    let mut t = Self::linear_pass(index as u8, &table);
                    // Negate point if either k1 or naf1[i] is negative.
                    t.conditional_negate(Choice::from(-(sign ^ s1) as u8));
                    t
                }
            };
            acc += t;

            let sign = naf2[i] >> 7;
            let index = ((naf2[i] ^ sign) - sign) >> 1;
            let mut t = match VARTIME {
                // Negate point if either k2 or naf2[i] is negative.
                true if sign != s2 => -table[index as usize],
                true => table[index as usize],
                false => {
                    let mut t = Self::linear_pass(index as u8, &table);
                    t.conditional_negate(Choice::from(-(sign ^ s2) as u8));
                    t
                }
            };
            t.x *= BETA_2.vartime::<VARTIME>();
            acc += t;
        }

        // If the subscalars were even, fix result here.
        let t = match VARTIME {
            true if s1 == -1 => -table[0],
            true => table[0],
            false => ConditionallySelectable::conditional_select(
                &table[0],
                &-table[0],
                Choice::from(-s1 as u8),
            ),
        };
        acc = match VARTIME {
            true if bit1 == 1 => acc,
            true => acc - t,
            false => G1Projective::conditional_select(&(acc - t), &acc, Choice::from(bit1))
        };
        table[0].x *= BETA_2.vartime::<VARTIME>();
        let t = match VARTIME {
            true if s2 == -1 => -table[0],
            true => table[0],
            false => ConditionallySelectable::conditional_select(
                &table[0],
                &-table[0],
                Choice::from(-s2 as u8),
            ),
        };
        match VARTIME {
            true if bit2 == 1 => acc,
            true => acc - t,
            false => G1Projective::conditional_select(&(acc - t), &acc, Choice::from(bit2)),
        }
    }

    /// Multiply `self` by `crate::BLS_X`, using double and add.
    fn mul_by_x(&self) -> Self {
        let mut xself = G1Projective::identity();
        // NOTE: in BLS12-381 we can just skip the first bit.
        let mut x = crate::BLS_X >> 1;
        let mut tmp = *self;
        while x != 0 {
            tmp = tmp.double();

            if x % 2 == 1 {
                xself += tmp;
            }
            x >>= 1;
        }
        // finally, flip the sign
        if crate::BLS_X_IS_NEGATIVE {
            xself = -xself;
        }
        xself
    }

    /// Multiplies by $(1 - z)$, where $z$ is the parameter of BLS12-381, which
    /// [suffices to clear](https://ia.cr/2019/403) the cofactor and map
    /// elliptic curve points to elements of $\mathbb{G}\_1$.
    pub fn clear_cofactor(&self) -> Self {
        self - self.mul_by_x()
    }

    /// Converts a batch of `G1Projective` elements into `G1Affine` elements. This
    /// function will panic if `p.len() != q.len()`.
    pub fn batch_normalize(p: &[Self], q: &mut [G1Affine<VARTIME>]) {
        assert_eq!(p.len(), q.len());

        let mut acc = Fp::one();
        for (p, q) in p.iter().zip(q.iter_mut()) {
            // We use the `x` field of `G1Affine` to store the product
            // of previous z-coordinates seen.
            q.x = acc;

            // We will end up skipping all identities in p
            acc = Fp::conditional_select(&(acc * p.z), &acc, p.is_identity());
        }

        // This is the inverse, as all z-coordinates are nonzero and the ones
        // that are not are skipped.
        acc = acc.invert().unwrap();

        for (p, q) in p.iter().rev().zip(q.iter_mut().rev()) {
            let skip = p.is_identity();

            // Compute tmp = 1/z
            let tmp = q.x * acc;

            // Cancel out z-coordinate in denominator of `acc`
            acc = Fp::conditional_select(&(acc * p.z), &acc, skip);

            // Set the coordinates to the correct value
            q.x = p.x * tmp;
            q.y = p.y * tmp;
            q.infinity = Choice::from(0u8);

            *q = G1Affine::conditional_select(q, &G1Affine::identity(), skip);
        }
    }

    /// Returns true if this point is on the curve. This should always return
    /// true unless an "unchecked" API was used.
    pub fn is_on_curve(&self) -> Choice {
        // Y^2 Z = X^3 + b Z^3
        let lhs = MulOp::mul(&MontOp::montgomery_reduce(&SquareOp::square(&self.y)), &self.z).montgomery_reduce_full();
        let x_3 = MulOp::mul(&MontOp::montgomery_reduce(&SquareOp::square(&self.x)), &self.x);
        let bz_3 = MulOp::mul(&MontOp::montgomery_reduce(&MulOp::mul(&MontOp::montgomery_reduce(&SquareOp::square(&self.z)), &self.z)), &B.vartime::<VARTIME>());
        let rhs = Ops::add(&x_3, &bz_3).montgomery_reduce_full();
        lhs.ct_eq(&rhs) | self.z.is_zero()
    }
}

#[derive(Clone, Copy)]
pub struct G1Compressed([u8; 48]);

impl fmt::Debug for G1Compressed {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0[..].fmt(f)
    }
}

impl Default for G1Compressed {
    fn default() -> Self {
        G1Compressed([0; 48])
    }
}

#[cfg(feature = "zeroize")]
impl zeroize::DefaultIsZeroes for G1Compressed {}

impl AsRef<[u8]> for G1Compressed {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsMut<[u8]> for G1Compressed {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl ConstantTimeEq for G1Compressed {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl Eq for G1Compressed {}
impl PartialEq for G1Compressed {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        bool::from(self.ct_eq(other))
    }
}

#[derive(Clone, Copy)]
pub struct G1Uncompressed([u8; 96]);

impl fmt::Debug for G1Uncompressed {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0[..].fmt(f)
    }
}

impl Default for G1Uncompressed {
    fn default() -> Self {
        G1Uncompressed([0; 96])
    }
}

#[cfg(feature = "zeroize")]
impl zeroize::DefaultIsZeroes for G1Uncompressed {}

impl AsRef<[u8]> for G1Uncompressed {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsMut<[u8]> for G1Uncompressed {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

impl ConstantTimeEq for G1Uncompressed {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl Eq for G1Uncompressed {}
impl PartialEq for G1Uncompressed {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        bool::from(self.ct_eq(other))
    }
}

impl Group for G1Projective {
    type Scalar = Scalar;

    fn random(mut rng: impl RngCore) -> Self {
        loop {
            let x = Fp::random(&mut rng);
            let flip_sign = rng.next_u32() % 2 != 0;

            // Obtain the corresponding y-coordinate given x as y = sqrt(x^3 + 4)
            let p = ((x.square() * x) + B).sqrt().map(|y| G1Affine {
                x,
                y: if flip_sign { -y } else { y },
                infinity: 0.into(),
            });

            if p.is_some().into() {
                let p = p.unwrap().to_curve().clear_cofactor();

                if bool::from(!p.is_identity()) {
                    return p;
                }
            }
        }
    }

    fn identity() -> Self {
        Self::identity()
    }

    fn generator() -> Self {
        Self::generator()
    }

    fn is_identity(&self) -> Choice {
        self.is_identity()
    }

    #[must_use]
    fn double(&self) -> Self {
        self.double()
    }
}

#[cfg(feature = "alloc")]
impl WnafGroup for G1Projective {
    fn recommended_wnaf_for_num_scalars(num_scalars: usize) -> usize {
        const RECOMMENDATIONS: [usize; 12] =
            [1, 3, 7, 20, 43, 120, 273, 563, 1630, 3128, 7933, 62569];

        let mut ret = 4;
        for r in &RECOMMENDATIONS {
            if num_scalars > *r {
                ret += 1;
            } else {
                break;
            }
        }

        ret
    }
}

impl PrimeGroup for G1Projective {}

impl Curve for G1Projective {
    type AffineRepr = G1Affine;

    fn batch_normalize(p: &[Self], q: &mut [Self::AffineRepr]) {
        Self::batch_normalize(p, q);
    }

    fn to_affine(&self) -> Self::AffineRepr {
        self.into()
    }
}

impl PrimeCurve for G1Projective {
    type Affine = G1Affine;
}

impl PrimeCurveAffine for G1Affine {
    type Scalar = Scalar;
    type Curve = G1Projective;

    fn identity() -> Self {
        Self::identity()
    }

    fn generator() -> Self {
        Self::generator()
    }

    fn is_identity(&self) -> Choice {
        self.is_identity()
    }

    fn to_curve(&self) -> Self::Curve {
        self.into()
    }
}

impl GroupEncoding for G1Projective {
    type Repr = G1Compressed;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        G1Affine::from_bytes(bytes).map(Self::from)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        G1Affine::from_bytes_unchecked(bytes).map(Self::from)
    }

    fn to_bytes(&self) -> Self::Repr {
        G1Affine::from(self).to_bytes()
    }
}

impl GroupEncoding for G1Affine {
    type Repr = G1Compressed;

    fn from_bytes(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed(&bytes.0)
    }

    fn from_bytes_unchecked(bytes: &Self::Repr) -> CtOption<Self> {
        Self::from_compressed_unchecked(&bytes.0)
    }

    fn to_bytes(&self) -> Self::Repr {
        G1Compressed(self.to_compressed())
    }
}

impl UncompressedEncoding for G1Affine {
    type Uncompressed = G1Uncompressed;

    fn from_uncompressed(bytes: &Self::Uncompressed) -> CtOption<Self> {
        Self::from_uncompressed(&bytes.0)
    }

    fn from_uncompressed_unchecked(bytes: &Self::Uncompressed) -> CtOption<Self> {
        Self::from_uncompressed_unchecked(&bytes.0)
    }

    fn to_uncompressed(&self) -> Self::Uncompressed {
        G1Uncompressed(self.to_uncompressed())
    }
}
#[cfg(test)]
mod test {
    use super::*;

#[test]
fn test_beta() {
    assert_eq!(
        BETA,
        Fp::from_bytes(&[
            0x00u8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5f, 0x19, 0x67, 0x2f, 0xdf, 0x76,
            0xce, 0x51, 0xba, 0x69, 0xc6, 0x07, 0x6a, 0x0f, 0x77, 0xea, 0xdd, 0xb3, 0xa9, 0x3b,
            0xe6, 0xf8, 0x96, 0x88, 0xde, 0x17, 0xd8, 0x13, 0x62, 0x0a, 0x00, 0x02, 0x2e, 0x01,
            0xff, 0xff, 0xff, 0xfe, 0xff, 0xfe
        ])
        .unwrap()
    );
    assert_ne!(BETA, Fp::one());
    assert_ne!(BETA * BETA, Fp::one());
    assert_eq!(BETA * BETA * BETA, Fp::one());
}
#[test]
fn test_is_on_curve() {
    assert!(bool::from(G1Affine::<false>::identity().is_on_curve()));
    assert!(bool::from(G1Affine::<false>::generator().is_on_curve()));
    assert!(bool::from(G1Projective::<false>::identity().is_on_curve()));
    assert!(bool::from(G1Projective::<false>::generator().is_on_curve()));

    let z: Fp = Fp::from_raw_unchecked([
        0xba7a_fa1f_9a6f_e250,
        0xfa0f_5b59_5eaf_e731,
        0x3bdc_4776_94c3_06e7,
        0x2149_be4b_3949_fa24,
        0x64aa_6e06_49b2_078c,
        0x12b1_08ac_3364_3c3e,
    ]);

    let gen: G1Affine = G1Affine::generator();
    let mut test = G1Projective {
        x: gen.x * z,
        y: gen.y * z,
        z,
    };

    assert!(bool::from(test.is_on_curve()));

    test.x = z;
    assert!(!bool::from(test.is_on_curve()));
}

#[test]
#[allow(clippy::eq_op)]
fn test_affine_point_equality() {
    let a: G1Affine = G1Affine::generator();
    let b = G1Affine::identity();

    assert!(a == a);
    assert!(b == b);
    assert!(a != b);
    assert!(b != a);
}

#[test]
#[allow(clippy::eq_op)]
fn test_projective_point_equality() {
    let a: G1Projective = G1Projective::generator();
    let b = G1Projective::identity();

    assert!(a == a);
    assert!(b == b);
    assert!(a != b);
    assert!(b != a);

    let z = Fp::from_raw_unchecked([
        0xba7a_fa1f_9a6f_e250,
        0xfa0f_5b59_5eaf_e731,
        0x3bdc_4776_94c3_06e7,
        0x2149_be4b_3949_fa24,
        0x64aa_6e06_49b2_078c,
        0x12b1_08ac_3364_3c3e,
    ]);

    let mut c = G1Projective {
        x: a.x * z,
        y: a.y * z,
        z,
    };
    assert!(bool::from(c.is_on_curve()));

    assert!(a == c);
    assert!(b != c);
    assert!(c == a);
    assert!(c != b);

    c.y = -c.y;
    assert!(bool::from(c.is_on_curve()));

    assert!(a != c);
    assert!(b != c);
    assert!(c != a);
    assert!(c != b);

    c.y = -c.y;
    c.x = z;
    assert!(!bool::from(c.is_on_curve()));
    assert!(a != b);
    assert!(a != c);
    assert!(b != c);
}

#[test]
fn test_conditionally_select_affine() {
    let a: G1Affine = G1Affine::generator();
    let b = G1Affine::identity();

    assert_eq!(G1Affine::conditional_select(&a, &b, Choice::from(0u8)), a);
    assert_eq!(G1Affine::conditional_select(&a, &b, Choice::from(1u8)), b);
}

#[test]
fn test_conditionally_select_projective() {
    let a: G1Projective = G1Projective::generator();
    let b = G1Projective::identity();

    assert_eq!(
        G1Projective::conditional_select(&a, &b, Choice::from(0u8)),
        a
    );
    assert_eq!(
        G1Projective::conditional_select(&a, &b, Choice::from(1u8)),
        b
    );
}

#[test]
fn test_projective_to_affine() {
    let a: G1Projective = G1Projective::generator();
    let b: G1Projective = G1Projective::identity();

    assert!(bool::from(G1Affine::from(a).is_on_curve()));
    assert!(!bool::from(G1Affine::from(a).is_identity()));
    assert!(bool::from(G1Affine::from(b).is_on_curve()));
    assert!(bool::from(G1Affine::from(b).is_identity()));

    let z = Fp::from_raw_unchecked([
        0xba7a_fa1f_9a6f_e250,
        0xfa0f_5b59_5eaf_e731,
        0x3bdc_4776_94c3_06e7,
        0x2149_be4b_3949_fa24,
        0x64aa_6e06_49b2_078c,
        0x12b1_08ac_3364_3c3e,
    ]);

    let c = G1Projective {
        x: a.x * z,
        y: a.y * z,
        z,
    };

    assert_eq!(G1Affine::from(c), G1Affine::generator());
}

#[test]
fn test_affine_to_projective() {
    let a: G1Affine = G1Affine::generator();
    let b: G1Affine = G1Affine::identity();

    assert!(bool::from(G1Projective::from(a).is_on_curve()));
    assert!(!bool::from(G1Projective::from(a).is_identity()));
    assert!(bool::from(G1Projective::from(b).is_on_curve()));
    assert!(bool::from(G1Projective::from(b).is_identity()));
}

#[test]
fn test_doubling() {
    {
        let tmp: G1Projective = G1Projective::identity().double();
        assert!(bool::from(tmp.is_identity()));
        assert!(bool::from(tmp.is_on_curve()));
    }
    {
        let tmp: G1Projective = G1Projective::generator().double();
        assert!(!bool::from(tmp.is_identity()));
        assert!(bool::from(tmp.is_on_curve()));

        assert_eq!(
            G1Affine::from(tmp),
            G1Affine {
                x: Fp::from_raw_unchecked([
                    0x53e9_78ce_58a9_ba3c,
                    0x3ea0_583c_4f3d_65f9,
                    0x4d20_bb47_f001_2960,
                    0xa54c_664a_e5b2_b5d9,
                    0x26b5_52a3_9d7e_b21f,
                    0x0008_895d_26e6_8785,
                ]),
                y: Fp::from_raw_unchecked([
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
        let a: G1Projective = G1Projective::identity();
        let mut b = G1Projective::generator();
        {
            let z = Fp::from_raw_unchecked([
                0xba7a_fa1f_9a6f_e250,
                0xfa0f_5b59_5eaf_e731,
                0x3bdc_4776_94c3_06e7,
                0x2149_be4b_3949_fa24,
                0x64aa_6e06_49b2_078c,
                0x12b1_08ac_3364_3c3e,
            ]);

            b = G1Projective {
                x: b.x * z,
                y: b.y * z,
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
            let z = Fp::from_raw_unchecked([
                0xba7a_fa1f_9a6f_e250,
                0xfa0f_5b59_5eaf_e731,
                0x3bdc_4776_94c3_06e7,
                0x2149_be4b_3949_fa24,
                0x64aa_6e06_49b2_078c,
                0x12b1_08ac_3364_3c3e,
            ]);

            b = G1Projective {
                x: b.x * z,
                y: b.y * z,
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
        let beta: Fp = Fp::from_raw_unchecked([
            0xcd03_c9e4_8671_f071,
            0x5dab_2246_1fcd_a5d2,
            0x5870_42af_d385_1b95,
            0x8eb6_0ebe_01ba_cb9e,
            0x03f9_7d6e_83d0_50d2,
            0x18f0_2065_5463_8741,
        ]);
        let beta = beta.square();
        let a = G1Projective::generator().double().double();
        let b = G1Projective {
            x: a.x * beta,
            y: -a.y,
            z: a.z,
        };
        assert!(bool::from(a.is_on_curve()));
        assert!(bool::from(b.is_on_curve()));

        let c = a + b;
        assert_eq!(
            G1Affine::from(c),
            G1Affine::from(G1Projective {
                x: Fp::from_raw_unchecked([
                    0x29e1_e987_ef68_f2d0,
                    0xc5f3_ec53_1db0_3233,
                    0xacd6_c4b6_ca19_730f,
                    0x18ad_9e82_7bc2_bab7,
                    0x46e3_b2c5_785c_c7a9,
                    0x07e5_71d4_2d22_ddd6,
                ]),
                y: Fp::from_raw_unchecked([
                    0x94d1_17a7_e5a5_39e7,
                    0x8e17_ef67_3d4b_5d22,
                    0x9d74_6aaf_508a_33ea,
                    0x8c6d_883d_2516_c9a2,
                    0x0bc3_b8d5_fb04_47f7,
                    0x07bf_a4c7_210f_4f44,
                ]),
                z: Fp::one()
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
        let c = a + b;
        assert!(bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
    }
    {
        let a: G1Affine = G1Affine::identity();
        let mut b: G1Projective = G1Projective::generator();
        {
            let z = Fp::from_raw_unchecked([
                0xba7a_fa1f_9a6f_e250,
                0xfa0f_5b59_5eaf_e731,
                0x3bdc_4776_94c3_06e7,
                0x2149_be4b_3949_fa24,
                0x64aa_6e06_49b2_078c,
                0x12b1_08ac_3364_3c3e,
            ]);

            b = G1Projective {
                x: b.x * z,
                y: b.y * z,
                z,
            };
        }
        let c = a + b;
        assert!(!bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
        assert!(c == G1Projective::generator());
    }
    {
        let a: G1Affine = G1Affine::identity();
        let mut b = G1Projective::generator();
        {
            let z = Fp::from_raw_unchecked([
                0xba7a_fa1f_9a6f_e250,
                0xfa0f_5b59_5eaf_e731,
                0x3bdc_4776_94c3_06e7,
                0x2149_be4b_3949_fa24,
                0x64aa_6e06_49b2_078c,
                0x12b1_08ac_3364_3c3e,
            ]);

            b = G1Projective {
                x: b.x * z,
                y: b.y * z,
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
            d += G1Affine::generator();
        }
        assert!(!bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
        assert!(!bool::from(d.is_identity()));
        assert!(bool::from(d.is_on_curve()));
        assert_eq!(c, d);
    }

    // Degenerate case
    {
        let beta: Fp = Fp::from_raw_unchecked([
            0xcd03_c9e4_8671_f071,
            0x5dab_2246_1fcd_a5d2,
            0x5870_42af_d385_1b95,
            0x8eb6_0ebe_01ba_cb9e,
            0x03f9_7d6e_83d0_50d2,
            0x18f0_2065_5463_8741,
        ]);
        let beta = beta.square();
        let a = G1Projective::generator().double().double();
        let b = G1Projective {
            x: a.x * beta,
            y: -a.y,
            z: a.z,
        };
        let a = G1Affine::from(a);
        assert!(bool::from(a.is_on_curve()));
        assert!(bool::from(b.is_on_curve()));

        let c = a + b;
        assert_eq!(
            G1Affine::from(c),
            G1Affine::from(G1Projective {
                x: Fp::from_raw_unchecked([
                    0x29e1_e987_ef68_f2d0,
                    0xc5f3_ec53_1db0_3233,
                    0xacd6_c4b6_ca19_730f,
                    0x18ad_9e82_7bc2_bab7,
                    0x46e3_b2c5_785c_c7a9,
                    0x07e5_71d4_2d22_ddd6,
                ]),
                y: Fp::from_raw_unchecked([
                    0x94d1_17a7_e5a5_39e7,
                    0x8e17_ef67_3d4b_5d22,
                    0x9d74_6aaf_508a_33ea,
                    0x8c6d_883d_2516_c9a2,
                    0x0bc3_b8d5_fb04_47f7,
                    0x07bf_a4c7_210f_4f44,
                ]),
                z: Fp::one()
            })
        );
        assert!(!bool::from(c.is_identity()));
        assert!(bool::from(c.is_on_curve()));
    }
}

#[test]
#[allow(clippy::eq_op)]
fn test_projective_negation_and_subtraction() {
    let a: G1Projective = G1Projective::generator().double();
    assert_eq!(a + (-a), G1Projective::identity());
    assert_eq!(a + (-a), a - a);
}

#[test]
fn test_affine_negation_and_subtraction() {
    let a: G1Affine = G1Affine::generator();
    assert_eq!(G1Projective::from(a) + (-a), G1Projective::identity());
    assert_eq!(G1Projective::from(a) + (-a), G1Projective::from(a) - a);
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

    assert_eq!((g * a) * b, g * c);
}

#[test]
fn test_affine_scalar_multiplication() {
    let g: G1Affine = G1Affine::generator();
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

    assert_eq!(G1Affine::from(g * a) * b, g * c);
}

#[test]
fn test_is_torsion_free() {
    let a: G1Affine = G1Affine {
        x: Fp::from_raw_unchecked([
            0x0aba_f895_b97e_43c8,
            0xba4c_6432_eb9b_61b0,
            0x1250_6f52_adfe_307f,
            0x7502_8c34_3933_6b72,
            0x8474_4f05_b8e9_bd71,
            0x113d_554f_b095_54f7,
        ]),
        y: Fp::from_raw_unchecked([
            0x73e9_0e88_f5cf_01c0,
            0x3700_7b65_dd31_97e2,
            0x5cf9_a199_2f0d_7c78,
            0x4f83_c10b_9eb3_330d,
            0xf6a6_3f6f_07f6_0961,
            0x0c53_b5b9_7e63_4df3,
        ]),
        infinity: Choice::from(0u8),
    };
    assert!(!bool::from(a.is_torsion_free()));

    assert!(bool::from(G1Affine::<false>::identity().is_torsion_free()));
    assert!(bool::from(G1Affine::<false>::generator().is_torsion_free()));
}

#[test]
fn test_mul_by_x() {
    // multiplying by `x` a point in G1 is the same as multiplying by
    // the equivalent scalar.
    let generator: G1Projective = G1Projective::generator();
    let x = if crate::BLS_X_IS_NEGATIVE {
        -Scalar::from(crate::BLS_X)
    } else {
        Scalar::from(crate::BLS_X)
    };
    assert_eq!(generator.mul_by_x(), generator * x);

    let point = G1Projective::generator() * Scalar::from(42);
    assert_eq!(point.mul_by_x(), point * x);
}

#[test]
fn test_clear_cofactor() {
    // the generator (and the identity) are always on the curve,
    // even after clearing the cofactor
    let generator: G1Projective = G1Projective::generator();
    assert!(bool::from(generator.clear_cofactor().is_on_curve()));
    let id: G1Projective = G1Projective::identity();
    assert!(bool::from(id.clear_cofactor().is_on_curve()));

    let z: Fp = Fp::from_raw_unchecked([
        0x3d2d1c670671394e,
        0x0ee3a800a2f7c1ca,
        0x270f4f21da2e5050,
        0xe02840a53f1be768,
        0x55debeb597512690,
        0x08bd25353dc8f791,
    ]);

    let point = G1Projective {
        x: Fp::from_raw_unchecked([
            0x48af5ff540c817f0,
            0xd73893acaf379d5a,
            0xe6c43584e18e023c,
            0x1eda39c30f188b3e,
            0xf618c6d3ccc0f8d8,
            0x0073542cd671e16c,
        ]) * z,
        y: Fp::from_raw_unchecked([
            0x57bf8be79461d0ba,
            0xfc61459cee3547c3,
            0x0d23567df1ef147b,
            0x0ee187bcce1d9b64,
            0xb0c8cfbe9dc8fdc1,
            0x1328661767ef368b,
        ]),
        z: z.square() * z,
    };

    assert!(bool::from(point.is_on_curve()));
    assert!(!bool::from(G1Affine::from(point).is_torsion_free()));
    let cleared_point = point.clear_cofactor();
    assert!(bool::from(cleared_point.is_on_curve()));
    assert!(bool::from(G1Affine::from(cleared_point).is_torsion_free()));

    // in BLS12-381 the cofactor in G1 can be
    // cleared multiplying by (1-x)
    let h_eff = Scalar::from(1) + Scalar::from(crate::BLS_X);
    assert_eq!(point.clear_cofactor(), point * h_eff);
}

#[test]
fn test_batch_normalize() {
    let a: G1Projective = G1Projective::generator().double();
    let b = a.double();
    let c = b.double();

    for a_identity in (0..=1).map(|n| n == 1) {
        for b_identity in (0..=1).map(|n| n == 1) {
            for c_identity in (0..=1).map(|n| n == 1) {
                let mut v = [a, b, c];
                if a_identity {
                    v[0] = G1Projective::identity()
                }
                if b_identity {
                    v[1] = G1Projective::identity()
                }
                if c_identity {
                    v[2] = G1Projective::identity()
                }

                let mut t = [
                    G1Affine::identity(),
                    G1Affine::identity(),
                    G1Affine::identity(),
                ];
                let expected = [
                    G1Affine::from(v[0]),
                    G1Affine::from(v[1]),
                    G1Affine::from(v[2]),
                ];

                G1Projective::batch_normalize(&v[..], &mut t[..]);

                assert_eq!(&t[..], &expected[..]);
            }
        }
    }
}

#[cfg(feature = "zeroize")]
#[test]
fn test_zeroize() {
    use zeroize::Zeroize;

    let mut a = G1Affine::generator();
    a.zeroize();
    assert!(bool::from(a.is_identity()));

    let mut a = G1Projective::generator();
    a.zeroize();
    assert!(bool::from(a.is_identity()));

    let mut a = GroupEncoding::to_bytes(&G1Affine::generator());
    a.zeroize();
    assert_eq!(&a, &G1Compressed::default());

    let mut a = UncompressedEncoding::to_uncompressed(&G1Affine::generator());
    a.zeroize();
    assert_eq!(&a, &G1Uncompressed::default());
}

#[test]
fn test_commutative_scalar_subgroup_multiplication() {
    let a: Scalar = Scalar::from_raw([
        0x1fff_3231_233f_fffd,
        0x4884_b7fa_0003_4802,
        0x998c_4fef_ecbc_4ff3,
        0x1824_b159_acc5_0562,
    ]);

    let g1_a = G1Affine::generator();
    let g1_p = G1Projective::generator();

    // By reference.
    assert_eq!(&g1_a * &a, &a * &g1_a);
    assert_eq!(&g1_p * &a, &a * &g1_p);

    // Mixed
    assert_eq!(&g1_a * a.clone(), a.clone() * &g1_a);
    assert_eq!(&g1_p * a.clone(), a.clone() * &g1_p);
    assert_eq!(g1_a.clone() * &a, &a * g1_a.clone());
    assert_eq!(g1_p.clone() * &a, &a * g1_p.clone());

    // By value.
    assert_eq!(g1_p * a, a * g1_p);
    assert_eq!(g1_a * a, a * g1_a);
}

#[test]
fn test_zero_double() {
    use rand_core::SeedableRng;
    let mut rng = rand_xorshift::XorShiftRng::from_seed([
        0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
        0xbc, 0xe5,
    ]);

    let one: Fp::<0, true> = Fp::one();
    let valv = -mul_by_3b(mul_by_3b::<true>(one.double() + one));

    for _ in 0..1_000_000 {
        let r = G1Projective{
            x: Fp::<0, true>::random(&mut rng),
            y: Fp::zero(),
            z: one,
        }.double();

        assert!(r.x.is_zero_vartime());
        assert_eq!(r.y, valv);
        assert!(r.z.is_zero_vartime());
    }
}
    
}
