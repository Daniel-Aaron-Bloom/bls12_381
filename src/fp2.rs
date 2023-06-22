//! This module implements arithmetic over the quadratic extension field Fp2.

use core::fmt;
use core::ops::{Add, Mul, MulAssign, Neg, Sub};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::fp::wide::{FpWideSub, FpWideAdd, FpWideReduce};
use crate::fp::{Fp, FpA, FpSub, FpAdd, FpMul, FpDouble};
use crate::util::{Mag, Never, OtherMag, DoubleOp, Ops, FpMagnitude, FpMag, ConstTime, Timing};

pub mod wide;

use self::wide::Fp2AWide;

#[derive(Copy, Clone)]
pub struct Fp2<const MAGNITUDE: usize = 0, const VARTIME: bool = false> {
    pub c0: Fp<MAGNITUDE, VARTIME>,
    pub c1: Fp<MAGNITUDE, VARTIME>,
}

#[derive(Copy, Clone)]
pub struct Fp2A<Mag0: FpMagnitude = FpMag<0>, Mag1: FpMagnitude = FpMag<0>, T: Timing = ConstTime> {
    pub c0: FpA<Mag0, T>,
    pub c1: FpA<Mag1, T>,
}

impl<const MAGNITUDE: usize, const VARTIME: bool> OtherMag for Fp2<MAGNITUDE, VARTIME> {
    const MAGNITUDE: usize = MAGNITUDE;
    type Mag<const MAG2: usize> = Fp2<MAG2, VARTIME>;
}

pub trait MirrorMag<Other> {
    type Mag;
}

impl<T> MirrorMag<Never> for T {
    type Mag = Never;
}
impl<const MAG1: usize, const MAG2: usize, const VARTIME: bool> MirrorMag<Fp<MAG2, VARTIME>> for Fp2<MAG1, VARTIME> {
    type Mag = Fp2<MAG2, VARTIME>;
}

impl<const MAGNITUDE: usize, const VARTIME: bool> Mag<2, [u64; 6]> for Fp2<MAGNITUDE, VARTIME>
where Fp<MAGNITUDE, VARTIME>: Mag<1, [u64; 6]>,
Self: MirrorMag<<Fp<MAGNITUDE, VARTIME> as Mag<1, [u64; 6]>>::Prev>,
Self: MirrorMag<<Fp<MAGNITUDE, VARTIME> as Mag<1, [u64; 6]>>::Next>,
<Self as MirrorMag<<Fp<MAGNITUDE, VARTIME> as Mag<1, [u64; 6]>>::Prev>>::Mag: Mag<2, [u64; 6]>,
<Self as MirrorMag<<Fp<MAGNITUDE, VARTIME> as Mag<1, [u64; 6]>>::Next>>::Mag: Mag<2, [u64; 6]>,
{
    type Prev = <Self as MirrorMag<<Fp<MAGNITUDE, VARTIME> as Mag<1, [u64; 6]>>::Prev>>::Mag;
    type Next = <Self as MirrorMag<<Fp<MAGNITUDE, VARTIME> as Mag<1, [u64; 6]>>::Next>>::Mag;
    const MODULUS: [u64; 6] = unimplemented!();

    #[inline(always)]
    fn make([c0, c1]: [[u64; 6]; 2]) -> Self {
        Self{ c0: Mag::make([c0]), c1: Mag::make([c1]) }
    }
    #[inline(always)]
    fn data(&self) -> [&[u64; 6]; 2] {
        [self.c0.data()[0], self.c1.data()[0]]
    }
    #[inline(always)]
    fn negate(&self) -> Self {
        Self {
            c0: self.c0.neg(),
            c1: self.c1.neg(),
        }
    }
}

impl<const MAG1: usize, const MAG2: usize, const VARTIME: bool> Ops<2, [u64; 6], Fp2<MAG2, VARTIME>> for Fp2<MAG1, VARTIME>
where Fp<MAG1, VARTIME>: Ops<1, [u64; 6], Fp<MAG2, VARTIME>>,
    <Fp<MAG1, VARTIME> as OtherMag>::Mag<MAG2>: Mag<1, [u64; 6]>,
    Fp2<MAG2, VARTIME>: Mag<2, [u64; 6]>,
{
    type OpOut = <Fp2<MAG2, VARTIME> as Mag<2, [u64; 6]>>::Next;
    #[inline(always)]
    fn add(lhs: &Self, rhs: &Fp2<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([
            *Ops::add(&lhs.c0, &Mag::make([rhs.c0.0])).data()[0],
            *Ops::add(&lhs.c1, &Mag::make([rhs.c1.0])).data()[0],
        ])
    }
    #[inline(always)]
    fn sub(lhs: &Self, rhs: &Fp2<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([
            *Ops::sub(&lhs.c0, &Mag::make([rhs.c0.0])).data()[0],
            *Ops::sub(&lhs.c1, &Mag::make([rhs.c1.0])).data()[0],
        ])
    }
}

impl<const POW: usize, const MAGNITUDE: usize, const VARTIME: bool> DoubleOp<POW> for Fp2<MAGNITUDE, VARTIME>
where Fp<MAGNITUDE, VARTIME>: DoubleOp<POW>,
<Fp<MAGNITUDE, VARTIME> as DoubleOp<POW>>::DoubleOut: Mag<1, [u64; 6]>,
Self: MirrorMag<<Fp<MAGNITUDE, VARTIME> as DoubleOp<POW>>::DoubleOut>,
<Self as MirrorMag<<Fp<MAGNITUDE, VARTIME> as DoubleOp<POW>>::DoubleOut>>::Mag: Mag<2, [u64; 6]>
{
    type DoubleOut = <Self as MirrorMag<<Fp<MAGNITUDE, VARTIME> as DoubleOp<POW>>::DoubleOut>>::Mag;
    fn double(lhs: &Self) -> Self::DoubleOut {
        Mag::make([
            *DoubleOp::<POW>::double(&lhs.c0).data()[0],
            *DoubleOp::<POW>::double(&lhs.c1).data()[0],
        ])
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> fmt::Debug for Fp2<MAGNITUDE, VARTIME> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} + {:?}*u", self.c0, self.c1)
    }
}

impl<Mag0: FpMagnitude, Mag1: FpMagnitude, T: Timing> fmt::Debug for Fp2A<Mag0, Mag1, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} + {:?}*u", self.c0, self.c1)
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> Default for Fp2<MAGNITUDE, VARTIME> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<Mag0: FpMagnitude, Mag1: FpMagnitude, T: Timing> Default for Fp2A<Mag0, Mag1, T> {
    fn default() -> Self {
        Self::zero()
    }
}

#[cfg(feature = "zeroize")]
impl<const MAGNITUDE: usize = 0, const VARTIME: bool = false> zeroize::DefaultIsZeroes for Fp2<MAGNITUDE, VARTIME> {}

#[cfg(feature = "zeroize")]
impl<Mag0: FpMagnitude, Mag1: FpMagnitude, T: Timing> zeroize::DefaultIsZeroes for Fp2A<Mag0, Mag1, T> {}

impl<const MAGNITUDE: usize, const VARTIME: bool> From<Fp<MAGNITUDE, VARTIME>> for Fp2<MAGNITUDE, VARTIME> {
    fn from(f: Fp<MAGNITUDE, VARTIME>) -> Self {
        Fp2 {
            c0: f,
            c1: Fp::zero(),
        }
    }
}

impl<Mag0: FpMagnitude, Mag1: FpMagnitude, T: Timing> From<FpA<Mag0, T>> for Fp2A<Mag0, Mag1, T> {
    fn from(f: FpA<Mag0, T>) -> Self {
        Self {
            c0: f,
            c1: FpA::zero(),
        }
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> ConstantTimeEq for Fp2<MAGNITUDE, VARTIME> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0.ct_eq(&other.c0) & self.c1.ct_eq(&other.c1)
    }
}

impl<Mag0: FpMagnitude, Mag1: FpMagnitude, T: Timing> ConstantTimeEq for Fp2A<Mag0, Mag1, T> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0.ct_eq(&other.c0) & self.c1.ct_eq(&other.c1)
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> Eq for Fp2<MAGNITUDE, VARTIME> {}
impl<const MAGNITUDE: usize, const VARTIME: bool> PartialEq for Fp2<MAGNITUDE, VARTIME> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if VARTIME {
            self.c0 == other.c0 && self.c1 == other.c1
        } else {
            bool::from(self.ct_eq(other))
        }
    }
}

impl<Mag0: FpMagnitude, Mag1: FpMagnitude, T: Timing> Eq for Fp2A<Mag0, Mag1, T> {}
impl<Mag0: FpMagnitude, Mag1: FpMagnitude, T: Timing> PartialEq for Fp2A<Mag0, Mag1, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if T::VAR {
            self.c0 == other.c0 && self.c1 == other.c1
        } else {
            bool::from(self.ct_eq(other))
        }
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> ConditionallySelectable for Fp2<MAGNITUDE, VARTIME> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fp2 {
            c0: Fp::conditional_select(&a.c0, &b.c0, choice),
            c1: Fp::conditional_select(&a.c1, &b.c1, choice),
        }
    }
}

impl<Mag0: FpMagnitude, Mag1: FpMagnitude, T: Timing> ConditionallySelectable for Fp2A<Mag0, Mag1, T> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fp2A {
            c0: FpA::conditional_select(&a.c0, &b.c0, choice),
            c1: FpA::conditional_select(&a.c1, &b.c1, choice),
        }
    }
}

impl<'a, const MAGNITUDE: usize, const VARTIME: bool> Neg for &'a Fp2<MAGNITUDE, VARTIME> {
    type Output = Fp2<MAGNITUDE, VARTIME>;

    #[inline]
    fn neg(self) -> Fp2<MAGNITUDE, VARTIME> {
        self.neg()
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> Neg for Fp2<MAGNITUDE, VARTIME> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        -&self
    }
}

impl<'a, 'b> Sub<&'b Fp2> for &'a Fp2 {
    type Output = Fp2;

    #[inline]
    fn sub(self, rhs: &'b Fp2) -> Fp2 {
        self.sub(rhs)
    }
}

impl<'a, 'b> Add<&'b Fp2> for &'a Fp2 {
    type Output = Fp2;

    #[inline]
    fn add(self, rhs: &'b Fp2) -> Fp2 {
        self.add(rhs)
    }
}

impl<'a, 'b> Mul<&'b Fp2> for &'a Fp2 {
    type Output = Fp2;

    #[inline]
    fn mul(self, rhs: &'b Fp2) -> Fp2 {
        self.mul(rhs)
    }
}

impl_binops_additive!(Fp2, Fp2);
impl_binops_multiplicative!(Fp2, Fp2);

impl<const MAGNITUDE: usize, const VARTIME: bool> Fp2<MAGNITUDE, VARTIME> {
    #[inline]
    pub const fn zero() -> Self {
        Fp2 {
            c0: Fp::zero(),
            c1: Fp::zero(),
        }
    }

    #[inline]
    pub const fn one() -> Self {
        Fp2 {
            c0: Fp::one(),
            c1: Fp::zero(),
        }
    }

    #[inline]
    pub const fn eq_vartime(&self, rhs: &Self) -> bool {
        self.c0.eq_vartime(&rhs.c0) && self.c1.eq_vartime(&rhs.c1)
    }

    #[inline]
    pub fn is_zero(&self) -> Choice {
        self.c0.is_zero() & self.c1.is_zero()
    }

    #[inline]
    pub const fn is_zero_vartime(&self) -> bool {
        self.c0.is_zero_vartime() & self.c1.is_zero_vartime()
    }

    #[inline(always)]
    pub const fn conjugate(&self) -> Self {
        Fp2 {
            c0: self.c0,
            c1: self.c1.neg(),
        }
    }

    /// Raises this element to p.
    #[inline(always)]
    pub const fn frobenius_map(&self) -> Self {
        // This is always just a conjugation. If you're curious why, here's
        // an article about it: https://alicebob.cryptoland.net/the-frobenius-endomorphism-with-finite-fields/
        self.conjugate()
    }

    #[inline(always)]
    pub const fn mul_by_nonresidue(&self) -> Self {
        // Multiply a + bu by u + 1, getting
        // au + a + bu^2 + bu
        // and because u^2 = -1, we get
        // (a - b) + (a + b)u

        Fp2 {
            c0: self.c0.sub(&self.c1),
            c1: self.c0.add(&self.c1),
        }
    }

    pub const fn square(&self) -> Self {
        // Complex squaring:
        //
        // v0  = c0 * c1
        // c0' = (c0 + c1) * (c0 + \beta*c1) - v0 - \beta * v0
        // c1' = 2 * v0
        //
        // In BLS12-381's F_{p^2}, our \beta is -1 so we
        // can modify this formula:
        //
        // c0' = (c0 + c1) * (c0 - c1)
        // c1' = 2 * c0 * c1

        let a = (&self.c0).add(&self.c1);
        let b = (&self.c0).sub(&self.c1);
        //let c = (&self.c0).add(&self.c0);
        let c = (&self.c0).double();

        Fp2 {
            c0: a.mul(&b),
            c1: c.mul(&self.c1),
        }
    }

    pub const fn mul(&self, rhs: &Self) -> Self {
        // F_{p^2} x F_{p^2} multiplication implemented with operand scanning (schoolbook)
        // computes the result as:
        //
        //   a·b = (a_0 b_0 + a_1 b_1 β) + (a_0 b_1 + a_1 b_0)i
        //
        // In BLS12-381's F_{p^2}, our β is -1, so the resulting F_{p^2} element is:
        //
        //   c_0 = a_0 b_0 - a_1 b_1
        //   c_1 = a_0 b_1 + a_1 b_0
        //
        // Each of these is a "sum of products", which we can compute efficiently.

        Fp2 {
            c0: Fp::sum_of_products([self.c0, self.c1.neg()], [rhs.c0, rhs.c1]),
            c1: Fp::sum_of_products([self.c0, self.c1], [rhs.c1, rhs.c0]),
        }
    }

    pub const fn add(&self, rhs: &Self) -> Self {
        Fp2 {
            c0: (&self.c0).add(&rhs.c0),
            c1: (&self.c1).add(&rhs.c1),
        }
    }

    pub const fn sub(&self, rhs: &Self) -> Self {
        Fp2 {
            c0: (&self.c0).sub(&rhs.c0),
            c1: (&self.c1).sub(&rhs.c1),
        }
    }

    pub const fn neg(&self) -> Self {
        Fp2 {
            c0: (&self.c0).neg(),
            c1: (&self.c1).neg(),
        }
    }

    /// Although this is labeled "vartime", it is only
    /// variable time with respect to the exponent. It
    /// is also not exposed in the public API.
    pub const fn pow_vartime(&self, by: &[u64; 6]) -> Self {
        let mut res = Self::one();
        // for e in by.iter().rev() {
        let mut e_i = by.len();
        while e_i > 0 {
            e_i -= 1;
            let e = &by[e_i];
            // for i in (0..64).rev() {
            let mut i = 64;
            while i > 0 {
                i -= 1;
                res = res.square();

                if ((*e >> i) & 1) == 1 {
                    res = res.mul(self);
                }
            }
        }
        res
    }

    /// Vartime exponentiation for larger exponents, only
    /// used in testing and not exposed through the public API.
    #[cfg(all(test, feature = "experimental"))]
    pub(crate) fn pow_vartime_extended(&self, by: &[u64]) -> Self {
        let mut res = Self::one();
        for e in by.iter().rev() {
            for i in (0..64).rev() {
                res = res.square();

                if ((*e >> i) & 1) == 1 {
                    res *= self;
                }
            }
        }
        res
    }

    /// a1 = self^((p - 3) / 4)
    #[inline]
    const fn sqrt_a1(&self) -> Self {
        self.pow_vartime(&[
            0xee7f_bfff_ffff_eaaa,
            0x07aa_ffff_ac54_ffff,
            0xd9cc_34a8_3dac_3d89,
            0xd91d_d2e1_3ce1_44af,
            0x92c6_e9ed_90d2_eb35,
            0x0680_447a_8e5f_f9a6,
        ])
    }

    /// (1 + alpha)^((q - 1) // 2) * x0
    #[inline]
    const fn sqrt_alpha(alpha: &Self, x0: &Self) -> Self {
        x0.mul(&(alpha.add(&Fp2::one())).pow_vartime(&[
            0xdcff_7fff_ffff_d555,
            0x0f55_ffff_58a9_ffff,
            0xb398_6950_7b58_7b12,
            0xb23b_a5c2_79c2_895f,
            0x258d_d3db_21a5_d66b,
            0x0d00_88f5_1cbf_f34d,
        ]))
    }

    pub fn sqrt(&self) -> CtOption<Self> {
        // Algorithm 9, https://eprint.iacr.org/2012/685.pdf
        // with constant time modifications.

        CtOption::new(Fp2::zero(), self.is_zero()).or_else(|| {
            // a1 = self^((p - 3) / 4)
            let a1 = self.sqrt_a1();

            // alpha = a1^2 * self = self^((p - 3) / 2 + 1) = self^((p - 1) / 2)
            let alpha = &self.mul(&a1.square());

            // x0 = self^((p + 1) / 4)
            let x0 = &self.mul(&a1);

            // In the event that alpha = -1, the element is order p - 1 and so
            // we're just trying to get the square of an element of the subfield
            // Fp. This is given by x0 * u, since u = sqrt(-1). Since the element
            // x0 = a + bu has b = 0, the solution is therefore au.
            CtOption::new(
                Fp2 {
                    c0: (&x0.c1).neg(),
                    c1: x0.c0,
                },
                alpha.ct_eq(&(&Fp2::one()).neg()),
            )
            // Otherwise, the correct solution is (1 + alpha)^((q - 1) // 2) * x0
            .or_else(|| {
                CtOption::new(
                    Self::sqrt_alpha(&alpha, &x0),
                    Choice::from(1),
                )
            })
            // Only return the result if it's really the square root (and so
            // self is actually quadratic nonresidue)
            .and_then(|sqrt| CtOption::new(sqrt, sqrt.square().ct_eq(self)))
        })
    }

    pub const fn sqrt_vartime(&self) -> Option<Self> {
        // Algorithm 9, https://eprint.iacr.org/2012/685.pdf

        // a1 = self^((p - 3) / 4)
        let a1 = self.sqrt_a1();

        // alpha = a1^2 * self = self^((p - 3) / 2 + 1) = self^((p - 1) / 2)
        let alpha = &self.mul(&a1.square());

        // x0 = self^((p + 1) / 4)
        let x0 = &self.mul(&a1);

        let sqrt = if alpha.eq_vartime(&(&Fp2::one()).neg()) {
            Fp2 {
                c0: (&x0.c1).neg(),
                c1: x0.c0,
            }
        } else {
            Self::sqrt_alpha(alpha, x0)
        };

        if sqrt.square().eq_vartime(self) {
            Some(sqrt)
        } else {
            None
        }
    }
    #[inline]
    const fn dot_self(&self) -> Fp<MAGNITUDE, VARTIME> {
        Fp::sum_of_squares([self.c0, self.c1])
    }

    /// Computes the multiplicative inverse of this field
    /// element, returning None in the case that this element
    /// is zero.
    pub fn invert(&self) -> CtOption<Self> {
        // We wish to find the multiplicative inverse of a nonzero
        // element a + bu in Fp2. We leverage an identity
        //
        // (a + bu)(a - bu) = a^2 + b^2
        //
        // which holds because u^2 = -1. This can be rewritten as
        //
        // (a + bu)(a - bu)/(a^2 + b^2) = 1
        //
        // because a^2 + b^2 = 0 has no nonzero solutions for (a, b).
        // This gives that (a - bu)/(a^2 + b^2) is the inverse
        // of (a + bu). Importantly, this can be computing using
        // only a single inversion in Fp.
        self.dot_self().invert().map(|t| Fp2 {
            c0: self.c0.mul(&t),
            c1: self.c1.mul(&t.neg()),
        })
    }

    /// Computes the multiplicative inverse of this field
    /// element, returning None in the case that this element
    /// is zero.
    pub const fn invert_vartime(&self) -> Option<Self> {
        // We wish to find the multiplicative inverse of a nonzero
        // element a + bu in Fp2. We leverage an identity
        //
        // (a + bu)(a - bu) = a^2 + b^2
        //
        // which holds because u^2 = -1. This can be rewritten as
        //
        // (a + bu)(a - bu)/(a^2 + b^2) = 1
        //
        // because a^2 + b^2 = 0 has no nonzero solutions for (a, b).
        // This gives that (a - bu)/(a^2 + b^2) is the inverse
        // of (a + bu). Importantly, this can be computing using
        // only a single inversion in Fp.
        match self.dot_self().invert_vartime() {
            Some(t) => Some(Fp2 {
                c0: self.c0.mul(&t),
                c1: self.c1.mul(&t.neg()),
            }),
            None => None,
        }
    }
}

pub type Fp2Square0<Mag0, Mag1> = FpMul<FpAdd<Mag0, Mag1>, FpSub<Mag0, Mag1>>;
pub type Fp2Square1<Mag0, Mag1> = FpMul<FpDouble<Mag0>, Mag1>;
pub type Fp2Mul0<Lhs0, Lhs1, Rhs0, Rhs1> = FpWideSub<FpMul<Lhs0, Rhs0>, FpMul<Lhs1, Rhs1>>;
pub type Fp2Mul1<Lhs0, Lhs1, Rhs0, Rhs1> = FpWideAdd<FpMul<Lhs0, Rhs1>, FpMul<Lhs1, Rhs0>>;
pub type Fp2Pow0<Mag0, Mag1> = FpWideReduce<FpMul<FpAdd<Mag0, Mag1>, FpSub<Mag0, Mag1>>>;
pub type Fp2Pow1<Mag0, Mag1> = FpWideReduce<FpMul<FpDouble<Mag0>, Mag1>>;
pub type Fp2SqrtASquare0<Mag0, Mag1> = FpWideReduce<Fp2Square0<Fp2Pow0<Mag0, Mag1>, Fp2Pow1<Mag0, Mag1>>>;
pub type Fp2SqrtASquare1<Mag0, Mag1> = FpWideReduce<Fp2Square1<Fp2Pow0<Mag0, Mag1>, Fp2Pow1<Mag0, Mag1>>>;
pub type Fp2SqrtAlpha0<Mag0, Mag1> = FpWideReduce<Fp2Mul0<Mag0, Mag1, Fp2SqrtASquare0<Mag0, Mag1>, Fp2SqrtASquare1<Mag0, Mag1>>>;
pub type Fp2SqrtAlpha1<Mag0, Mag1> = FpWideReduce<Fp2Mul1<Mag0, Mag1, Fp2SqrtASquare0<Mag0, Mag1>, Fp2SqrtASquare1<Mag0, Mag1>>>;
pub type Fp2SqrtX0<Mag0, Mag1> = FpWideReduce<Fp2Mul0<Mag0, Mag1, Fp2Pow0<Mag0, Mag1>, Fp2Pow1<Mag0, Mag1>>>;
pub type Fp2SqrtX1<Mag0, Mag1> = FpWideReduce<Fp2Mul1<Mag0, Mag1, Fp2Pow0<Mag0, Mag1>, Fp2Pow1<Mag0, Mag1>>>;
pub type Fp2SqrtAlphaX0<Mag0, Mag1, XMag0, XMag1> = FpWideReduce<Fp2Mul0<Fp2Pow0<FpAdd<Mag0, FpMag<0>>, Mag1>, Fp2Pow1<FpAdd<Mag0, FpMag<0>>, Mag1>, XMag0, XMag1>>;
pub type Fp2SqrtAlphaX1<Mag0, Mag1, XMag0, XMag1> = FpWideReduce<Fp2Mul1<Fp2Pow0<FpAdd<Mag0, FpMag<0>>, Mag1>, Fp2Pow1<FpAdd<Mag0, FpMag<0>>, Mag1>, XMag0, XMag1>>;
// pub type Fp2SqrtAlphaX1<Mag0, Mag1, XMag0, XMag1> = Fp2Pow1<FpWideReduce<Fp2Mul0<FpAdd<Mag0, FpMag<0>>, Mag1, XMag0, XMag1>>, FpWideReduce<Fp2Mul1<FpAdd<Mag0, FpMag<0>>, Mag1, XMag0, XMag1>>>;
pub type Fp2Sqrt0<Mag0, Mag1> = Fp2SqrtAlphaX0<Fp2SqrtAlpha0<Mag0, Mag1>, Fp2SqrtAlpha1<Mag0, Mag1>, Fp2SqrtX0<Mag0, Mag1>, Fp2SqrtX1<Mag0, Mag1>>;
pub type Fp2Sqrt1<Mag0, Mag1> = Fp2SqrtAlphaX1<Fp2SqrtAlpha0<Mag0, Mag1>, Fp2SqrtAlpha1<Mag0, Mag1>, Fp2SqrtX0<Mag0, Mag1>, Fp2SqrtX1<Mag0, Mag1>>;

impl<Mag0: FpMagnitude, Mag1: FpMagnitude, T: Timing> Fp2A<Mag0, Mag1, T> {
    #[inline]
    pub const fn zero() -> Self {
        Self {
            c0: FpA::zero(),
            c1: FpA::zero(),
        }
    }

    #[inline]
    pub const fn one() -> Self {
        Self {
            c0: FpA::one(),
            c1: FpA::zero(),
        }
    }

    pub(crate) fn random(mut rng: impl RngCore) -> Self {
        Self {
            c0: FpA::random(&mut rng),
            c1: FpA::random(&mut rng),
        }
    }

    /// Returns one, the multiplicative identity.
    #[inline]
    pub const fn vartime<T2: Timing>(self) -> Fp2A<Mag0, Mag1, T2> {
        Fp2A{
            c0: self.c0.vartime(),
            c1: self.c1.vartime(),
        }
    }

    /// Reduce the magnitude of an `Fp`
    #[inline]
    pub const fn mag<MagR0, MagR1>(self) -> Fp2A<MagR0, MagR1, T>
    where MagR0: FpMagnitude, MagR1: FpMagnitude {
        Fp2A{
            c0: self.c0.mag(),
            c1: self.c1.mag(),
        }
    }

    #[inline]
    pub const fn eq_vartime(&self, rhs: &Self) -> bool {
        self.c0.eq_vartime(&rhs.c0) && self.c1.eq_vartime(&rhs.c1)
    }

    #[inline]
    pub fn is_zero(&self) -> Choice {
        self.c0.is_zero() & self.c1.is_zero()
    }

    #[inline]
    pub const fn is_zero_vartime(&self) -> bool {
        self.c0.is_zero_vartime() & self.c1.is_zero_vartime()
    }

    #[inline(always)]
    pub const fn conjugate(&self) -> Self {
        Self {
            c0: self.c0,
            c1: self.c1.neg(),
        }
    }

    /// Raises this element to p.
    #[inline(always)]
    pub const fn frobenius_map(&self) -> Self {
        // This is always just a conjugation. If you're curious why, here's
        // an article about it: https://alicebob.cryptoland.net/the-frobenius-endomorphism-with-finite-fields/
        self.conjugate()
    }

    #[inline(always)]
    pub const fn mul_by_nonresidue(&self) -> Fp2A<FpSub<Mag0, Mag1>, FpAdd<Mag0, Mag1>, T> {
        // Multiply a + bu by u + 1, getting
        // au + a + bu^2 + bu
        // and because u^2 = -1, we get
        // (a - b) + (a + b)u

        Fp2A {
            c0: self.c0.sub(&self.c1),
            c1: self.c0.add(&self.c1),
        }
    }

    pub const fn neg(&self) -> Self {
        Self {
            c0: self.c0.neg(),
            c1: self.c1.neg(),
        }
    }

    pub const fn add<RMag0, RMag1>(&self, rhs: &Fp2A<RMag0, RMag1, T>) -> Fp2A<FpAdd<Mag0, RMag0>, FpAdd<Mag1, RMag1>, T>
    where RMag0: FpMagnitude, RMag1: FpMagnitude {
        Fp2A {
            c0: self.c0.add(&rhs.c0),
            c1: self.c1.add(&rhs.c1),
        }
    }

    pub const fn add_fp<RMag>(&self, rhs: &FpA<RMag, T>) -> Fp2A<FpAdd<Mag0, RMag>, Mag1, T>
    where RMag: FpMagnitude {
        Fp2A {
            c0: self.c0.add(&rhs),
            c1: self.c1,
        }
    }

    pub const fn sub<RMag0, RMag1>(&self, rhs: &Fp2A<RMag0, RMag1, T>) -> Fp2A<FpSub<Mag0, RMag0>, FpSub<Mag1, RMag1>, T>
    where RMag0: FpMagnitude, RMag1: FpMagnitude {
        Fp2A {
            c0: self.c0.sub(&rhs.c0),
            c1: self.c1.sub(&rhs.c1),
        }
    }

    pub const fn square(&self) -> Fp2AWide<Fp2Square0<Mag0, Mag1>, Fp2Square1<Mag0, Mag1>, T> {
        // Complex squaring:
        //
        // v0  = c0 * c1
        // c0' = (c0 + c1) * (c0 + \beta*c1) - v0 - \beta * v0
        // c1' = 2 * v0
        //
        // In BLS12-381's F_{p^2}, our \beta is -1 so we
        // can modify this formula:
        //
        // c0' = (c0 + c1) * (c0 - c1)
        // c1' = 2 * c0 * c1

        let a = self.c0.add(&self.c1);
        let b = self.c0.sub(&self.c1);
        let c = self.c0.double();

        Fp2AWide {
            c0: a.mul(&b),
            c1: c.mul(&self.c1),
        }
    }

    pub const fn mul<RMag0, RMag1>(&self, rhs: &Fp2A<RMag0, RMag1, T>) -> Fp2AWide<
        Fp2Mul0<Mag0, Mag1, RMag0, RMag1>,
        Fp2Mul1<Mag0, Mag1, RMag0, RMag1>,
        T>
    where RMag0: FpMagnitude, RMag1: FpMagnitude {
        // F_{p^2} x F_{p^2} multiplication implemented with operand scanning (schoolbook)
        // computes the result as:
        //
        //   a·b = (a_0 b_0 + a_1 b_1 β) + (a_0 b_1 + a_1 b_0)i
        //
        // In BLS12-381's F_{p^2}, our β is -1, so the resulting F_{p^2} element is:
        //
        //   c_0 = a_0 b_0 - a_1 b_1
        //   c_1 = a_0 b_1 + a_1 b_0
        //
        // Each of these is a "sum of products", which we can compute efficiently.

        let c0 = self.c0.mul(&rhs.c0).sub(&self.c1.mul(&rhs.c1));
        let c1 = self.c0.mul(&rhs.c1).add(&self.c1.mul(&rhs.c0));
        Fp2AWide { c0, c1 }
    }

    /// Although this is labeled "vartime", it is only
    /// variable time with respect to the exponent. It
    /// is also not exposed in the public API.
    pub const fn pow_vartime(&self, by: &[u64; 6]) -> Fp2A<
        Fp2Pow0<Mag0, Mag1>,
        Fp2Pow1<Mag0, Mag1>,
        T> {
        let mut res = Fp2A::one();
        // for e in by.iter().rev() {
        let mut e_i = by.len();
        while e_i > 0 {
            e_i -= 1;
            let e = &by[e_i];
            // for i in (0..64).rev() {
            let mut i = 64;
            while i > 0 {
                i -= 1;
                res = res.square().montgomery_reduce().mag();

                if ((*e >> i) & 1) == 1 {
                    res = res.mul(self).montgomery_reduce().mag();
                }
            }
        }
        res
    }

    /// Although this is labeled "vartime", it is only
    /// variable time with respect to the exponent. It
    /// is also not exposed in the public API.
    #[cfg(all(test, feature = "experimental"))]
    pub const fn pow_vartime_extended(&self, by: &[u64]) -> Fp2A<
        Fp2Pow0<Mag0, Mag1>,
        Fp2Pow1<Mag0, Mag1>,
        T> {
        let mut res = Fp2A::one();
        // for e in by.iter().rev() {
        let mut e_i = by.len();
        while e_i > 0 {
            e_i -= 1;
            let e = &by[e_i];
            // for i in (0..64).rev() {
            let mut i = 64;
            while i > 0 {
                i -= 1;
                res = res.square().montgomery_reduce().reduce_full();

                if ((*e >> i) & 1) == 1 {
                    res = res.mul(self).montgomery_reduce().reduce_full();
                }
            }
        }
        res
    }

    /// alpha = self^((p - 1) / 2)
    #[inline]
    const fn sqrt_alpha_x(&self) -> (Fp2A<Fp2SqrtAlpha0<Mag0, Mag1>, Fp2SqrtAlpha1<Mag0, Mag1>, T>, Fp2A<Fp2SqrtX0<Mag0, Mag1>, Fp2SqrtX1<Mag0, Mag1>, T>) {
        // a1 = self^((p - 3) / 4)
        let a1 = self.pow_vartime(&[
            0xee7f_bfff_ffff_eaaa,
            0x07aa_ffff_ac54_ffff,
            0xd9cc_34a8_3dac_3d89,
            0xd91d_d2e1_3ce1_44af,
            0x92c6_e9ed_90d2_eb35,
            0x0680_447a_8e5f_f9a6,
        ]);

        // alpha = a1^2 * self = self^((p - 3) / 2 + 1) = self^((p - 1) / 2)
        let alpha = self.mul(&a1.square().montgomery_reduce()).montgomery_reduce();

        // x0 = self^((p + 1) / 4)
        let x0 = self.mul(&a1).montgomery_reduce();

        (alpha.mag::<FpMag<0>, FpMag<0>>().mag(), x0.mag::<FpMag<0>, FpMag<0>>().mag())
    }

    /// (1 + alpha)^((q - 1) // 2) * x0
    #[inline]
    const fn sqrt_alpha_times_x<XMag0, XMag1>(alpha: &Self, x0: &Fp2A<XMag0, XMag1, T>) -> Fp2A<Fp2SqrtAlphaX0<Mag0, Mag1, XMag0, XMag1>, Fp2SqrtAlphaX1<Mag0, Mag1, XMag0, XMag1>, T>
    where XMag0: FpMagnitude, XMag1: FpMagnitude {
        let one = FpA::<FpMag<0>, T>::one();
        alpha.add_fp(&one)
            .pow_vartime(&[
                0xdcff_7fff_ffff_d555,
                0x0f55_ffff_58a9_ffff,
                0xb398_6950_7b58_7b12,
                0xb23b_a5c2_79c2_895f,
                0x258d_d3db_21a5_d66b,
                0x0d00_88f5_1cbf_f34d,
            ])
            .mul(x0)
            .montgomery_reduce()
    }

    pub fn sqrt(&self) -> CtOption<Fp2A<Fp2Sqrt0<Mag0, Mag1>, Fp2Sqrt1<Mag0, Mag1>, T>> {
        // Algorithm 9, https://eprint.iacr.org/2012/685.pdf
        // with constant time modifications.

        // alpha = self^((p - 1) / 2)
        // x0 = self^((p + 1) / 4)
        let (alpha, x0) = self.sqrt_alpha_x();

        let zero = CtOption::new(Fp2A::zero(), self.is_zero());
        // In the event that alpha = -1, the element is order p - 1 and so
        // we're just trying to get the square of an element of the subfield
        // Fp. This is given by x0 * u, since u = sqrt(-1). Since the element
        // x0 = a + bu has b = 0, the solution is therefore au.
        let neg_1 = CtOption::new(
            Fp2A {
                c0: (&x0.c1).neg(),
                c1: x0.c0,
            }.mag(),
            alpha.add_fp::<FpMag<0>>(&FpA::one()).is_zero(),
        );
        // Otherwise, the correct solution is (1 + alpha)^((q - 1) // 2) * x0
        let sqrt = CtOption::new(
            Fp2A::sqrt_alpha_times_x(&alpha, &x0),
            Choice::from(1),
        );

        let sqrt = zero.or_else(|| neg_1 ).or_else(|| sqrt);
        // Only return the result if it's really the square root (and so
        // self is actually quadratic nonresidue)
        sqrt.and_then(|sqrt| CtOption::new(sqrt, sqrt.square().montgomery_reduce().sub(self).is_zero()))
    }

    pub const fn sqrt_vartime(&self) -> Option<Fp2A<Fp2Sqrt0<Mag0, Mag1>, Fp2Sqrt1<Mag0, Mag1>, T>> {
        // Algorithm 9, https://eprint.iacr.org/2012/685.pdf

        if self.is_zero_vartime() {
            return Some(Fp2A::zero())
        }

        // alpha = self^((p - 1) / 2)
        // x0 = self^((p + 1) / 4)
        let (alpha, x0) = self.sqrt_alpha_x();

        // In the event that alpha = -1, the element is order p - 1 and so
        // we're just trying to get the square of an element of the subfield
        // Fp. This is given by x0 * u, since u = sqrt(-1). Since the element
        // x0 = a + bu has b = 0, the solution is therefore au.
        let sqrt = if alpha.add_fp::<FpMag<0>>(&FpA::one()).is_zero_vartime() {
            Fp2A {
                c0: x0.c1.neg(),
                c1: x0.c0,
            }.mag()
        } else {
            // Otherwise, the correct solution is (1 + alpha)^((q - 1) // 2) * x0
            Fp2A::sqrt_alpha_times_x(&alpha, &x0)
        };

        // Only return the result if it's really the square root (and so
        // self is actually quadratic nonresidue)
        if sqrt.square().montgomery_reduce().sub(self).is_zero_vartime() {
            Some(sqrt)
        } else {
            None
        }
    }


}

impl Fp2 {
    pub(crate) fn random(mut rng: impl RngCore) -> Fp2 {
        Fp2 {
            c0: Fp::random(&mut rng),
            c1: Fp::random(&mut rng),
        }
    }

    /// Returns whether or not this element is strictly lexicographically
    /// larger than its negation.
    #[inline]
    pub const fn lexicographically_largest_vartime(&self) -> bool {
        // If this element's c1 coefficient is lexicographically largest
        // then it is lexicographically largest. Otherwise, in the event
        // the c1 coefficient is zero and the c0 coefficient is
        // lexicographically largest, then this element is lexicographically
        // largest.

        self.c1.lexicographically_largest_vartime()
            || (self.c1.is_zero_vartime() && self.c0.lexicographically_largest_vartime())
    }

    /// Returns whether or not this element is strictly lexicographically
    /// larger than its negation.
    #[inline]
    pub fn lexicographically_largest(&self) -> Choice {
        // If this element's c1 coefficient is lexicographically largest
        // then it is lexicographically largest. Otherwise, in the event
        // the c1 coefficient is zero and the c0 coefficient is
        // lexicographically largest, then this element is lexicographically
        // largest.

        self.c1.lexicographically_largest()
            | (self.c1.is_zero() & self.c0.lexicographically_largest())
    }

    /// Computes the multiplicative inverse of this field
    /// element, returning None in the case that this element
    /// is zero.
    pub fn invert2(&self) -> CtOption<Self> {
        // We wish to find the multiplicative inverse of a nonzero
        // element a + bu in Fp2. We leverage an identity
        //
        // (a + bu)(a - bu) = a^2 + b^2
        //
        // which holds because u^2 = -1. This can be rewritten as
        //
        // (a + bu)(a - bu)/(a^2 + b^2) = 1
        //
        // because a^2 + b^2 = 0 has no nonzero solutions for (a, b).
        // This gives that (a - bu)/(a^2 + b^2) is the inverse
        // of (a + bu). Importantly, this can be computing using
        // only a single inversion in Fp.

        (self.c0.square_wide() + self.c1.square_wide())
            .montgomery_reduce_full()
            .invert()
            .map(|t| Fp2 {
                c0: self.c0 * t,
                c1: self.c1 * -t,
            })
    }
}

#[cfg(test)]
mod test {
    use rand_core::{RngCore, SeedableRng};
    use super::*;

    fn gen_big(mut rng: impl RngCore) -> Fp2 {
        Fp2{
            c0: crate::fp::test::gen_big(&mut rng),
            c1: crate::fp::test::gen_big(&mut rng),
        }
    }
    fn gen_big_a(mut rng: impl RngCore) -> Fp2A {
        Fp2A{
            c0: crate::fp::test::gen_big_a(&mut rng),
            c1: crate::fp::test::gen_big_a(&mut rng),
        }
    }
    fn gen_big_both(mut rng: impl RngCore) -> (Fp2, Fp2A) {
        let c0 = crate::fp::test::gen_big_both(&mut rng);
        let c1 = crate::fp::test::gen_big_both(&mut rng);
        (Fp2{c0: c0.0, c1: c1.0}, Fp2A{c0: c0.1, c1: c1.1})
    }

    #[test]
    fn test_conditional_selection() {
        let a: Fp2 = Fp2 {
            c0: Fp::from_raw_unchecked([1, 2, 3, 4, 5, 6]),
            c1: Fp::from_raw_unchecked([7, 8, 9, 10, 11, 12]),
        };
        let b = Fp2 {
            c0: Fp::from_raw_unchecked([13, 14, 15, 16, 17, 18]),
            c1: Fp::from_raw_unchecked([19, 20, 21, 22, 23, 24]),
        };

        assert_eq!(
            ConditionallySelectable::conditional_select(&a, &b, Choice::from(0u8)),
            a
        );
        assert_eq!(
            ConditionallySelectable::conditional_select(&a, &b, Choice::from(1u8)),
            b
        );
    }

    #[test]
    fn test_equality() {
        fn is_equal(a: &Fp2, b: &Fp2) -> bool {
            let eq = a == b;
            let ct_eq = a.ct_eq(&b);

            assert_eq!(eq, bool::from(ct_eq));

            eq
        }

        assert!(is_equal(
            &Fp2 {
                c0: Fp::from_raw_unchecked([1, 2, 3, 4, 5, 6]),
                c1: Fp::from_raw_unchecked([7, 8, 9, 10, 11, 12]),
            },
            &Fp2 {
                c0: Fp::from_raw_unchecked([1, 2, 3, 4, 5, 6]),
                c1: Fp::from_raw_unchecked([7, 8, 9, 10, 11, 12]),
            }
        ));

        assert!(!is_equal(
            &Fp2 {
                c0: Fp::from_raw_unchecked([2, 2, 3, 4, 5, 6]),
                c1: Fp::from_raw_unchecked([7, 8, 9, 10, 11, 12]),
            },
            &Fp2 {
                c0: Fp::from_raw_unchecked([1, 2, 3, 4, 5, 6]),
                c1: Fp::from_raw_unchecked([7, 8, 9, 10, 11, 12]),
            }
        ));

        assert!(!is_equal(
            &Fp2 {
                c0: Fp::from_raw_unchecked([1, 2, 3, 4, 5, 6]),
                c1: Fp::from_raw_unchecked([2, 8, 9, 10, 11, 12]),
            },
            &Fp2 {
                c0: Fp::from_raw_unchecked([1, 2, 3, 4, 5, 6]),
                c1: Fp::from_raw_unchecked([7, 8, 9, 10, 11, 12]),
            }
        ));
    }

    #[test]
    fn test_squaring() {
        let a: Fp2 = Fp2 {
            c0: Fp::from_raw_unchecked([
                0xc9a2_1831_63ee_70d4,
                0xbc37_70a7_196b_5c91,
                0xa247_f8c1_304c_5f44,
                0xb01f_c2a3_726c_80b5,
                0xe1d2_93e5_bbd9_19c9,
                0x04b7_8e80_020e_f2ca,
            ]),
            c1: Fp::from_raw_unchecked([
                0x952e_a446_0462_618f,
                0x238d_5edd_f025_c62f,
                0xf6c9_4b01_2ea9_2e72,
                0x03ce_24ea_c1c9_3808,
                0x0559_50f9_45da_483c,
                0x010a_768d_0df4_eabc,
            ]),
        };
        let b = Fp2 {
            c0: Fp::from_raw_unchecked([
                0xa1e0_9175_a4d2_c1fe,
                0x8b33_acfc_204e_ff12,
                0xe244_15a1_1b45_6e42,
                0x61d9_96b1_b6ee_1936,
                0x1164_dbe8_667c_853c,
                0x0788_557a_cc7d_9c79,
            ]),
            c1: Fp::from_raw_unchecked([
                0xda6a_87cc_6f48_fa36,
                0x0fc7_b488_277c_1903,
                0x9445_ac4a_dc44_8187,
                0x0261_6d5b_c909_9209,
                0xdbed_4677_2db5_8d48,
                0x11b9_4d50_76c7_b7b1,
            ]),
        };

        assert_eq!(a.square(), b);

        let mut rng = rand_xorshift::XorShiftRng::from_seed([
            0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        for _ in 0..1_000 {
            let va = gen_big_a(&mut rng);
            let d1 = va.square().montgomery_reduce();
            let d2 = va.mul(&va).montgomery_reduce();
            let diff = d1.sub(&d2);
            assert!(diff.is_zero_vartime());
        }
        for i in 0..1_000_000 {
            if i == 100183 {
                println!("test")
            }
            let va: Fp2A = Fp2A::random(&mut rng);
            let d1 = va.square().montgomery_reduce();
            let d2 = va.mul(&va).montgomery_reduce();
            let diff = d1.sub(&d2);
            let x: Fp2A = diff.mag();
            assert!(diff.is_zero_vartime(), "{i} {x:?}");
        }
    }

    #[test]
    fn test_squaring_a() {
        let a: Fp2A = Fp2A {
            c0: FpA::from_raw_unchecked([
                0xc9a2_1831_63ee_70d4,
                0xbc37_70a7_196b_5c91,
                0xa247_f8c1_304c_5f44,
                0xb01f_c2a3_726c_80b5,
                0xe1d2_93e5_bbd9_19c9,
                0x04b7_8e80_020e_f2ca,
            ]),
            c1: FpA::from_raw_unchecked([
                0x952e_a446_0462_618f,
                0x238d_5edd_f025_c62f,
                0xf6c9_4b01_2ea9_2e72,
                0x03ce_24ea_c1c9_3808,
                0x0559_50f9_45da_483c,
                0x010a_768d_0df4_eabc,
            ]),
        };
        let b = Fp2A {
            c0: FpA::from_raw_unchecked([
                0xa1e0_9175_a4d2_c1fe,
                0x8b33_acfc_204e_ff12,
                0xe244_15a1_1b45_6e42,
                0x61d9_96b1_b6ee_1936,
                0x1164_dbe8_667c_853c,
                0x0788_557a_cc7d_9c79,
            ]),
            c1: FpA::from_raw_unchecked([
                0xda6a_87cc_6f48_fa36,
                0x0fc7_b488_277c_1903,
                0x9445_ac4a_dc44_8187,
                0x0261_6d5b_c909_9209,
                0xdbed_4677_2db5_8d48,
                0x11b9_4d50_76c7_b7b1,
            ]),
        };

        assert_eq!(a.square().montgomery_reduce(), b);
    }

    #[test]
    fn test_multiplication() {
        let a = Fp2 {
            c0: Fp::from_raw_unchecked([
                0xc9a2_1831_63ee_70d4,
                0xbc37_70a7_196b_5c91,
                0xa247_f8c1_304c_5f44,
                0xb01f_c2a3_726c_80b5,
                0xe1d2_93e5_bbd9_19c9,
                0x04b7_8e80_020e_f2ca,
            ]),
            c1: Fp::from_raw_unchecked([
                0x952e_a446_0462_618f,
                0x238d_5edd_f025_c62f,
                0xf6c9_4b01_2ea9_2e72,
                0x03ce_24ea_c1c9_3808,
                0x0559_50f9_45da_483c,
                0x010a_768d_0df4_eabc,
            ]),
        };
        let b = Fp2 {
            c0: Fp::from_raw_unchecked([
                0xa1e0_9175_a4d2_c1fe,
                0x8b33_acfc_204e_ff12,
                0xe244_15a1_1b45_6e42,
                0x61d9_96b1_b6ee_1936,
                0x1164_dbe8_667c_853c,
                0x0788_557a_cc7d_9c79,
            ]),
            c1: Fp::from_raw_unchecked([
                0xda6a_87cc_6f48_fa36,
                0x0fc7_b488_277c_1903,
                0x9445_ac4a_dc44_8187,
                0x0261_6d5b_c909_9209,
                0xdbed_4677_2db5_8d48,
                0x11b9_4d50_76c7_b7b1,
            ]),
        };
        let c = Fp2 {
            c0: Fp::from_raw_unchecked([
                0xf597_483e_27b4_e0f7,
                0x610f_badf_811d_ae5f,
                0x8432_af91_7714_327a,
                0x6a9a_9603_cf88_f09e,
                0xf05a_7bf8_bad0_eb01,
                0x0954_9131_c003_ffae,
            ]),
            c1: Fp::from_raw_unchecked([
                0x963b_02d0_f93d_37cd,
                0xc95c_e1cd_b30a_73d4,
                0x3087_25fa_3126_f9b8,
                0x56da_3c16_7fab_0d50,
                0x6b50_86b5_f4b6_d6af,
                0x09c3_9f06_2f18_e9f2,
            ]),
        };

        assert_eq!(a * b, c);
    }

    #[test]
    fn test_multiplication_a() {
        let a: Fp2A = Fp2A {
            c0: FpA::from_raw_unchecked([
                0xc9a2_1831_63ee_70d4,
                0xbc37_70a7_196b_5c91,
                0xa247_f8c1_304c_5f44,
                0xb01f_c2a3_726c_80b5,
                0xe1d2_93e5_bbd9_19c9,
                0x04b7_8e80_020e_f2ca,
            ]),
            c1: FpA::from_raw_unchecked([
                0x952e_a446_0462_618f,
                0x238d_5edd_f025_c62f,
                0xf6c9_4b01_2ea9_2e72,
                0x03ce_24ea_c1c9_3808,
                0x0559_50f9_45da_483c,
                0x010a_768d_0df4_eabc,
            ]),
        };
        let b: Fp2A = Fp2A {
            c0: FpA::from_raw_unchecked([
                0xa1e0_9175_a4d2_c1fe,
                0x8b33_acfc_204e_ff12,
                0xe244_15a1_1b45_6e42,
                0x61d9_96b1_b6ee_1936,
                0x1164_dbe8_667c_853c,
                0x0788_557a_cc7d_9c79,
            ]),
            c1: FpA::from_raw_unchecked([
                0xda6a_87cc_6f48_fa36,
                0x0fc7_b488_277c_1903,
                0x9445_ac4a_dc44_8187,
                0x0261_6d5b_c909_9209,
                0xdbed_4677_2db5_8d48,
                0x11b9_4d50_76c7_b7b1,
            ]),
        };
        let c: Fp2A = Fp2A {
            c0: FpA::from_raw_unchecked([
                0xf597_483e_27b4_e0f7,
                0x610f_badf_811d_ae5f,
                0x8432_af91_7714_327a,
                0x6a9a_9603_cf88_f09e,
                0xf05a_7bf8_bad0_eb01,
                0x0954_9131_c003_ffae,
            ]),
            c1: FpA::from_raw_unchecked([
                0x963b_02d0_f93d_37cd,
                0xc95c_e1cd_b30a_73d4,
                0x3087_25fa_3126_f9b8,
                0x56da_3c16_7fab_0d50,
                0x6b50_86b5_f4b6_d6af,
                0x09c3_9f06_2f18_e9f2,
            ]),
        };

        assert_eq!(a.mul(&b).montgomery_reduce().mag(), c);
    }

    #[test]
    fn test_addition() {
        let a = Fp2 {
            c0: Fp::from_raw_unchecked([
                0xc9a2_1831_63ee_70d4,
                0xbc37_70a7_196b_5c91,
                0xa247_f8c1_304c_5f44,
                0xb01f_c2a3_726c_80b5,
                0xe1d2_93e5_bbd9_19c9,
                0x04b7_8e80_020e_f2ca,
            ]),
            c1: Fp::from_raw_unchecked([
                0x952e_a446_0462_618f,
                0x238d_5edd_f025_c62f,
                0xf6c9_4b01_2ea9_2e72,
                0x03ce_24ea_c1c9_3808,
                0x0559_50f9_45da_483c,
                0x010a_768d_0df4_eabc,
            ]),
        };
        let b = Fp2 {
            c0: Fp::from_raw_unchecked([
                0xa1e0_9175_a4d2_c1fe,
                0x8b33_acfc_204e_ff12,
                0xe244_15a1_1b45_6e42,
                0x61d9_96b1_b6ee_1936,
                0x1164_dbe8_667c_853c,
                0x0788_557a_cc7d_9c79,
            ]),
            c1: Fp::from_raw_unchecked([
                0xda6a_87cc_6f48_fa36,
                0x0fc7_b488_277c_1903,
                0x9445_ac4a_dc44_8187,
                0x0261_6d5b_c909_9209,
                0xdbed_4677_2db5_8d48,
                0x11b9_4d50_76c7_b7b1,
            ]),
        };
        let c = Fp2 {
            c0: Fp::from_raw_unchecked([
                0x6b82_a9a7_08c1_32d2,
                0x476b_1da3_39ba_5ba4,
                0x848c_0e62_4b91_cd87,
                0x11f9_5955_295a_99ec,
                0xf337_6fce_2255_9f06,
                0x0c3f_e3fa_ce8c_8f43,
            ]),
            c1: Fp::from_raw_unchecked([
                0x6f99_2c12_73ab_5bc5,
                0x3355_1366_17a1_df33,
                0x8b0e_f74c_0aed_aff9,
                0x062f_9246_8ad2_ca12,
                0xe146_9770_738f_d584,
                0x12c3_c3dd_84bc_a26d,
            ]),
        };

        assert_eq!(a + b, c);
    }

    #[test]
    fn test_subtraction() {
        let a = Fp2 {
            c0: Fp::from_raw_unchecked([
                0xc9a2_1831_63ee_70d4,
                0xbc37_70a7_196b_5c91,
                0xa247_f8c1_304c_5f44,
                0xb01f_c2a3_726c_80b5,
                0xe1d2_93e5_bbd9_19c9,
                0x04b7_8e80_020e_f2ca,
            ]),
            c1: Fp::from_raw_unchecked([
                0x952e_a446_0462_618f,
                0x238d_5edd_f025_c62f,
                0xf6c9_4b01_2ea9_2e72,
                0x03ce_24ea_c1c9_3808,
                0x0559_50f9_45da_483c,
                0x010a_768d_0df4_eabc,
            ]),
        };
        let b = Fp2 {
            c0: Fp::from_raw_unchecked([
                0xa1e0_9175_a4d2_c1fe,
                0x8b33_acfc_204e_ff12,
                0xe244_15a1_1b45_6e42,
                0x61d9_96b1_b6ee_1936,
                0x1164_dbe8_667c_853c,
                0x0788_557a_cc7d_9c79,
            ]),
            c1: Fp::from_raw_unchecked([
                0xda6a_87cc_6f48_fa36,
                0x0fc7_b488_277c_1903,
                0x9445_ac4a_dc44_8187,
                0x0261_6d5b_c909_9209,
                0xdbed_4677_2db5_8d48,
                0x11b9_4d50_76c7_b7b1,
            ]),
        };
        let c = Fp2 {
            c0: Fp::from_raw_unchecked([
                0xe1c0_86bb_bf1b_5981,
                0x4faf_c3a9_aa70_5d7e,
                0x2734_b5c1_0bb7_e726,
                0xb2bd_7776_af03_7a3e,
                0x1b89_5fb3_98a8_4164,
                0x1730_4aef_6f11_3cec,
            ]),
            c1: Fp::from_raw_unchecked([
                0x74c3_1c79_9519_1204,
                0x3271_aa54_79fd_ad2b,
                0xc9b4_7157_4915_a30f,
                0x65e4_0313_ec44_b8be,
                0x7487_b238_5b70_67cb,
                0x0952_3b26_d0ad_19a4,
            ]),
        };

        assert_eq!(a - b, c);
    }

    #[test]
    fn test_negation() {
        let a: Fp2 = Fp2 {
            c0: Fp::from_raw_unchecked([
                0xc9a2_1831_63ee_70d4,
                0xbc37_70a7_196b_5c91,
                0xa247_f8c1_304c_5f44,
                0xb01f_c2a3_726c_80b5,
                0xe1d2_93e5_bbd9_19c9,
                0x04b7_8e80_020e_f2ca,
            ]),
            c1: Fp::from_raw_unchecked([
                0x952e_a446_0462_618f,
                0x238d_5edd_f025_c62f,
                0xf6c9_4b01_2ea9_2e72,
                0x03ce_24ea_c1c9_3808,
                0x0559_50f9_45da_483c,
                0x010a_768d_0df4_eabc,
            ]),
        };
        let b = Fp2 {
            c0: Fp::from_raw_unchecked([
                0xf05c_e7ce_9c11_39d7,
                0x6274_8f57_97e8_a36d,
                0xc4e8_d9df_c664_96df,
                0xb457_88e1_8118_9209,
                0x6949_13d0_8772_930d,
                0x1549_836a_3770_f3cf,
            ]),
            c1: Fp::from_raw_unchecked([
                0x24d0_5bb9_fb9d_491c,
                0xfb1e_a120_c12e_39d0,
                0x7067_879f_c807_c7b1,
                0x60a9_269a_31bb_dab6,
                0x45c2_56bc_fd71_649b,
                0x18f6_9b5d_2b8a_fbde,
            ]),
        };

        assert_eq!(-a, b);
    }

    #[test]
    fn test_sqrt() {
        // a = 1488924004771393321054797166853618474668089414631333405711627789629391903630694737978065425271543178763948256226639*u + 784063022264861764559335808165825052288770346101304131934508881646553551234697082295473567906267937225174620141295
        let a: Fp2 = Fp2 {
            c0: Fp::from_raw_unchecked([
                0x2bee_d146_27d7_f9e9,
                0xb661_4e06_660e_5dce,
                0x06c4_cc7c_2f91_d42c,
                0x996d_7847_4b7a_63cc,
                0xebae_bc4c_820d_574e,
                0x1886_5e12_d93f_d845,
            ]),
            c1: Fp::from_raw_unchecked([
                0x7d82_8664_baf4_f566,
                0xd17e_6639_96ec_7339,
                0x679e_ad55_cb40_78d0,
                0xfe3b_2260_e001_ec28,
                0x3059_93d0_43d9_1b68,
                0x0626_f03c_0489_b72d,
            ]),
        };

        assert_eq!(a.sqrt().unwrap().square(), a);
        assert_eq!(a.sqrt_vartime().unwrap().square(), a);
        

        // b = 5, which is a generator of the p - 1 order
        // multiplicative subgroup
        let b: Fp2 = Fp2 {
            c0: Fp::from_raw_unchecked([
                0x6631_0000_0010_5545,
                0x2114_0040_0eec_000d,
                0x3fa7_af30_c820_e316,
                0xc52a_8b8d_6387_695d,
                0x9fb4_e61d_1e83_eac5,
                0x005c_b922_afe8_4dc7,
            ]),
            c1: Fp::zero(),
        };

        assert_eq!(b.sqrt().unwrap().square(), b);
        assert_eq!(b.sqrt_vartime().unwrap().square(), b);

        // c = 25, which is a generator of the (p - 1) / 2 order
        // multiplicative subgroup
        let c: Fp2 = Fp2 {
            c0: Fp::from_raw_unchecked([
                0x44f6_0000_0051_ffae,
                0x86b8_0141_9948_0043,
                0xd715_9952_f1f3_794a,
                0x755d_6e3d_fe1f_fc12,
                0xd36c_d6db_5547_e905,
                0x02f8_c8ec_bf18_67bb,
            ]),
            c1: Fp::zero(),
        };

        assert_eq!(c.sqrt().unwrap().square(), c);
        assert_eq!(c.sqrt_vartime().unwrap().square(), c);

        // 2155129644831861015726826462986972654175647013268275306775721078997042729172900466542651176384766902407257452753362*u + 2796889544896299244102912275102369318775038861758288697415827248356648685135290329705805931514906495247464901062529
        // is nonsquare.
        assert!(bool::from(
            Fp2::<0, false> {
                c0: Fp::from_raw_unchecked([
                    0xc5fa_1bc8_fd00_d7f6,
                    0x3830_ca45_4606_003b,
                    0x2b28_7f11_04b1_02da,
                    0xa7fb_30f2_8230_f23e,
                    0x339c_db9e_e953_dbf0,
                    0x0d78_ec51_d989_fc57,
                ]),
                c1: Fp::from_raw_unchecked([
                    0x27ec_4898_cf87_f613,
                    0x9de1_394e_1abb_05a5,
                    0x0947_f85d_c170_fc14,
                    0x586f_bc69_6b61_14b7,
                    0x2b34_75a4_077d_7169,
                    0x13e1_c895_cc4b_6c22,
                ])
            }
            .sqrt()
            .is_none()
        ));
        assert!(bool::from(
            Fp2::<0, false> {
                c0: Fp::from_raw_unchecked([
                    0xc5fa_1bc8_fd00_d7f6,
                    0x3830_ca45_4606_003b,
                    0x2b28_7f11_04b1_02da,
                    0xa7fb_30f2_8230_f23e,
                    0x339c_db9e_e953_dbf0,
                    0x0d78_ec51_d989_fc57,
                ]),
                c1: Fp::from_raw_unchecked([
                    0x27ec_4898_cf87_f613,
                    0x9de1_394e_1abb_05a5,
                    0x0947_f85d_c170_fc14,
                    0x586f_bc69_6b61_14b7,
                    0x2b34_75a4_077d_7169,
                    0x13e1_c895_cc4b_6c22,
                ])
            }
            .sqrt_vartime()
            .is_none()
        ));
    }


    #[test]
    fn test_sqrt_a() {
        // a = 1488924004771393321054797166853618474668089414631333405711627789629391903630694737978065425271543178763948256226639*u + 784063022264861764559335808165825052288770346101304131934508881646553551234697082295473567906267937225174620141295
        let a: Fp2A = Fp2A {
            c0: FpA::from_raw_unchecked([
                0x2bee_d146_27d7_f9e9,
                0xb661_4e06_660e_5dce,
                0x06c4_cc7c_2f91_d42c,
                0x996d_7847_4b7a_63cc,
                0xebae_bc4c_820d_574e,
                0x1886_5e12_d93f_d845,
            ]),
            c1: FpA::from_raw_unchecked([
                0x7d82_8664_baf4_f566,
                0xd17e_6639_96ec_7339,
                0x679e_ad55_cb40_78d0,
                0xfe3b_2260_e001_ec28,
                0x3059_93d0_43d9_1b68,
                0x0626_f03c_0489_b72d,
            ]),
        };

        assert_eq!(a.sqrt_vartime().unwrap().square().montgomery_reduce().mag(), a);
        assert_eq!(a.sqrt().unwrap().square().montgomery_reduce().mag(), a);
        

        // b = 5, which is a generator of the p - 1 order
        // multiplicative subgroup
        let b: Fp2 = Fp2 {
            c0: Fp::from_raw_unchecked([
                0x6631_0000_0010_5545,
                0x2114_0040_0eec_000d,
                0x3fa7_af30_c820_e316,
                0xc52a_8b8d_6387_695d,
                0x9fb4_e61d_1e83_eac5,
                0x005c_b922_afe8_4dc7,
            ]),
            c1: Fp::zero(),
        };

        assert_eq!(b.sqrt().unwrap().square(), b);
        assert_eq!(b.sqrt_vartime().unwrap().square(), b);

        // c = 25, which is a generator of the (p - 1) / 2 order
        // multiplicative subgroup
        let c: Fp2 = Fp2 {
            c0: Fp::from_raw_unchecked([
                0x44f6_0000_0051_ffae,
                0x86b8_0141_9948_0043,
                0xd715_9952_f1f3_794a,
                0x755d_6e3d_fe1f_fc12,
                0xd36c_d6db_5547_e905,
                0x02f8_c8ec_bf18_67bb,
            ]),
            c1: Fp::zero(),
        };

        assert_eq!(c.sqrt().unwrap().square(), c);
        assert_eq!(c.sqrt_vartime().unwrap().square(), c);

        // 2155129644831861015726826462986972654175647013268275306775721078997042729172900466542651176384766902407257452753362*u + 2796889544896299244102912275102369318775038861758288697415827248356648685135290329705805931514906495247464901062529
        // is nonsquare.
        assert!(bool::from(
            Fp2::<0, false> {
                c0: Fp::from_raw_unchecked([
                    0xc5fa_1bc8_fd00_d7f6,
                    0x3830_ca45_4606_003b,
                    0x2b28_7f11_04b1_02da,
                    0xa7fb_30f2_8230_f23e,
                    0x339c_db9e_e953_dbf0,
                    0x0d78_ec51_d989_fc57,
                ]),
                c1: Fp::from_raw_unchecked([
                    0x27ec_4898_cf87_f613,
                    0x9de1_394e_1abb_05a5,
                    0x0947_f85d_c170_fc14,
                    0x586f_bc69_6b61_14b7,
                    0x2b34_75a4_077d_7169,
                    0x13e1_c895_cc4b_6c22,
                ])
            }
            .sqrt()
            .is_none()
        ));
        assert!(bool::from(
            Fp2::<0, false> {
                c0: Fp::from_raw_unchecked([
                    0xc5fa_1bc8_fd00_d7f6,
                    0x3830_ca45_4606_003b,
                    0x2b28_7f11_04b1_02da,
                    0xa7fb_30f2_8230_f23e,
                    0x339c_db9e_e953_dbf0,
                    0x0d78_ec51_d989_fc57,
                ]),
                c1: Fp::from_raw_unchecked([
                    0x27ec_4898_cf87_f613,
                    0x9de1_394e_1abb_05a5,
                    0x0947_f85d_c170_fc14,
                    0x586f_bc69_6b61_14b7,
                    0x2b34_75a4_077d_7169,
                    0x13e1_c895_cc4b_6c22,
                ])
            }
            .sqrt_vartime()
            .is_none()
        ));
    }

    #[test]
    fn test_inversion() {
        let a: Fp2 = Fp2 {
            c0: Fp::from_raw_unchecked([
                0x1128_ecad_6754_9455,
                0x9e7a_1cff_3a4e_a1a8,
                0xeb20_8d51_e08b_cf27,
                0xe98a_d408_11f5_fc2b,
                0x736c_3a59_232d_511d,
                0x10ac_d42d_29cf_cbb6,
            ]),
            c1: Fp::from_raw_unchecked([
                0xd328_e37c_c2f5_8d41,
                0x948d_f085_8a60_5869,
                0x6032_f9d5_6f93_a573,
                0x2be4_83ef_3fff_dc87,
                0x30ef_61f8_8f48_3c2a,
                0x1333_f55a_3572_5be0,
            ]),
        };

        let b = Fp2 {
            c0: Fp::from_raw_unchecked([
                0x0581_a133_3d4f_48a6,
                0x5824_2f6e_f074_8500,
                0x0292_c955_349e_6da5,
                0xba37_721d_dd95_fcd0,
                0x70d1_6790_3aa5_dfc5,
                0x1189_5e11_8b58_a9d5,
            ]),
            c1: Fp::from_raw_unchecked([
                0x0eda_09d2_d7a8_5d17,
                0x8808_e137_a7d1_a2cf,
                0x43ae_2625_c1ff_21db,
                0xf85a_c9fd_f7a7_4c64,
                0x8fcc_dda5_b8da_9738,
                0x08e8_4f0c_b32c_d17d,
            ]),
        };

        assert_eq!(a.invert().unwrap(), b);

        assert!(bool::from(Fp2::<0, false>::zero().invert().is_none()));
    }

    #[test]
    fn test_lexicographic_largest() {
        assert!(!bool::from(Fp2::zero().lexicographically_largest()));
        assert!(!bool::from(Fp2::one().lexicographically_largest()));
        assert!(bool::from(
            Fp2 {
                c0: Fp::from_raw_unchecked([
                    0x1128_ecad_6754_9455,
                    0x9e7a_1cff_3a4e_a1a8,
                    0xeb20_8d51_e08b_cf27,
                    0xe98a_d408_11f5_fc2b,
                    0x736c_3a59_232d_511d,
                    0x10ac_d42d_29cf_cbb6,
                ]),
                c1: Fp::from_raw_unchecked([
                    0xd328_e37c_c2f5_8d41,
                    0x948d_f085_8a60_5869,
                    0x6032_f9d5_6f93_a573,
                    0x2be4_83ef_3fff_dc87,
                    0x30ef_61f8_8f48_3c2a,
                    0x1333_f55a_3572_5be0,
                ]),
            }
            .lexicographically_largest()
        ));
        assert!(!bool::from(
            Fp2 {
                c0: -Fp::from_raw_unchecked([
                    0x1128_ecad_6754_9455,
                    0x9e7a_1cff_3a4e_a1a8,
                    0xeb20_8d51_e08b_cf27,
                    0xe98a_d408_11f5_fc2b,
                    0x736c_3a59_232d_511d,
                    0x10ac_d42d_29cf_cbb6,
                ]),
                c1: -Fp::from_raw_unchecked([
                    0xd328_e37c_c2f5_8d41,
                    0x948d_f085_8a60_5869,
                    0x6032_f9d5_6f93_a573,
                    0x2be4_83ef_3fff_dc87,
                    0x30ef_61f8_8f48_3c2a,
                    0x1333_f55a_3572_5be0,
                ]),
            }
            .lexicographically_largest()
        ));
        assert!(!bool::from(
            Fp2 {
                c0: Fp::from_raw_unchecked([
                    0x1128_ecad_6754_9455,
                    0x9e7a_1cff_3a4e_a1a8,
                    0xeb20_8d51_e08b_cf27,
                    0xe98a_d408_11f5_fc2b,
                    0x736c_3a59_232d_511d,
                    0x10ac_d42d_29cf_cbb6,
                ]),
                c1: Fp::zero(),
            }
            .lexicographically_largest()
        ));
        assert!(bool::from(
            Fp2 {
                c0: -Fp::from_raw_unchecked([
                    0x1128_ecad_6754_9455,
                    0x9e7a_1cff_3a4e_a1a8,
                    0xeb20_8d51_e08b_cf27,
                    0xe98a_d408_11f5_fc2b,
                    0x736c_3a59_232d_511d,
                    0x10ac_d42d_29cf_cbb6,
                ]),
                c1: Fp::zero(),
            }
            .lexicographically_largest()
        ));
    }

    #[cfg(feature = "zeroize")]
    #[test]
    fn test_zeroize() {
        use zeroize::Zeroize;

        let mut a = Fp2::one();
        a.zeroize();
        assert!(bool::from(a.is_zero()));
    }
}