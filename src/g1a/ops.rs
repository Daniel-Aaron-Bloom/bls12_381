use core::{fmt, ops::{Neg, Add, Sub}};

use subtle::{Choice, ConstantTimeEq, ConditionallySelectable};

use crate::{fp::FpA, util::{Timing, ConstTime, VarTime}};

use super::*;

impl Default for G1Affine {
    fn default() -> G1Affine {
        G1Affine::identity()
    }
}

#[cfg(feature = "zeroize")]
impl zeroize::DefaultIsZeroes for G1Affine {}

impl<'a, T: Timing> From<&'a G1Projective<T>> for G1Affine<T> {
    fn from(p: &'a G1Projective<T>) -> G1Affine<T> {
        let zinv = p.z.invert().unwrap_or(FpA::zero());
        let x = p.x.mul(&zinv).montgomery_reduce().mag();
        let y = p.y.mul(&zinv).montgomery_reduce().mag();

        let tmp = G1Affine {
            x,
            y,
            infinity: T::from_bool(false),
        };

        G1Affine::conditional_select(&tmp, &G1Affine::identity(), zinv.is_zero())
    }
}

impl<T: Timing> From<G1Projective<T>> for G1Affine<T> {
    fn from(p: G1Projective<T>) -> G1Affine<T> {
        From::from(&p)
    }
}

impl<T: Timing> fmt::Display for G1Affine<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<T: Timing> ConstantTimeEq for G1Affine<T> {
    fn ct_eq(&self, other: &Self) -> Choice {
        // The only cases in which two points are equal are
        // 1. infinity is set on both
        // 2. infinity is not set on both, and their coordinates are equal
        let lhs = T::to_choice(self.infinity);
        let rhs = T::to_choice(other.infinity);

        (lhs & rhs) | ((!lhs) & (!rhs)
                & self.x.ct_eq(&other.x)
                & self.y.ct_eq(&other.y))
    }
}

impl<T: Timing> ConditionallySelectable for G1Affine<T> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        G1Affine {
            x: FpA::conditional_select(&a.x, &b.x, choice),
            y: FpA::conditional_select(&a.y, &b.y, choice),
            infinity: T::from_choice(Choice::conditional_select(&T::to_choice(a.infinity), &T::to_choice(b.infinity), choice)),
        }
    }
}

impl<T: Timing> Eq for G1Affine<T>
where Self: PartialEq {}
impl PartialEq for G1Affine<ConstTime> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        bool::from(self.ct_eq(other))
    }
}

impl PartialEq for G1Affine<VarTime> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.x == other.x && self.y == other.y && self.infinity == other.infinity
    }
}

impl<'a> Neg for &'a G1Affine<ConstTime> {
    type Output = G1Affine<ConstTime>;

    #[inline]
    fn neg(self) -> G1Affine<ConstTime> {
        G1Affine {
            x: self.x,
            y: FpA::conditional_select(&self.y.neg(), &FpA::one(), self.infinity),
            infinity: self.infinity,
        }
    }
}

impl<'a> Neg for &'a G1Affine<VarTime> {
    type Output = G1Affine<VarTime>;

    #[inline]
    fn neg(self) -> G1Affine<VarTime> {
        self.const_neg()
    }
}

impl<T: Timing> Neg for G1Affine<T>
where for<'a> &'a G1Affine<T>: Neg<Output = G1Affine<T>> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        -&self
    }
}

impl<'a, 'b, T: Timing> Add<&'b G1Projective<T>> for &'a G1Affine<T> {
    type Output = G1Projective<T>;

    #[inline]
    fn add(self, rhs: &'b G1Projective<T>) -> G1Projective<T> {
        rhs.add_mixed(self)
    }
}

impl<'a, 'b, T: Timing> Add<&'b G1Affine<T>> for &'a G1Projective<T> {
    type Output = G1Projective<T>;

    #[inline]
    fn add(self, rhs: &'b G1Affine<T>) -> G1Projective<T> {
        self.add_mixed(rhs)
    }
}


impl<T: Timing> Default for G1Projective<T> {
    fn default() -> Self {
        G1Projective::identity()
    }
}

#[cfg(feature = "zeroize")]
impl<T: Timing> zeroize::DefaultIsZeroes for G1Projective<T> {}

impl<'a, T: Timing> From<&'a G1Affine<T>> for G1Projective<T> {
    fn from(p: &'a G1Affine<T>) -> Self {
        G1Projective {
            x: p.x,
            y: p.y,
            z: FpA::conditional_select(&FpA::one(), &FpA::zero(), T::to_choice(p.infinity)),
        }
    }
}

impl<T: Timing> From<G1Affine<T>> for G1Projective<T> {
    fn from(p: G1Affine<T>) -> Self {
        G1Projective::from(&p)
    }
}

impl<T: Timing> fmt::Display for G1Projective<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<T: Timing> ConstantTimeEq for G1Projective<T> {
    fn ct_eq(&self, other: &Self) -> Choice {
        // Is (xz, yz, z) equal to (x'z', y'z', z') when converted to affine?

        let x1 = self.x.mul(&other.z).montgomery_reduce();
        let x2 = other.x.mul(&self.z).montgomery_reduce();

        let y1 = self.y.mul(&other.z).montgomery_reduce();
        let y2 = other.y.mul(&self.z).montgomery_reduce();

        let self_is_zero = self.z.is_zero();
        let other_is_zero = other.z.is_zero();

        (self_is_zero & other_is_zero) // Both point at infinity
            | ((!self_is_zero) & (!other_is_zero) & x1.ct_eq(&x2) & y1.ct_eq(&y2))
        // Neither point at infinity, coordinates are the same
    }
}

impl<T: Timing> ConditionallySelectable for G1Projective<T> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        G1Projective {
            x: FpA::conditional_select(&a.x, &b.x, choice),
            y: FpA::conditional_select(&a.y, &b.y, choice),
            z: FpA::conditional_select(&a.z, &b.z, choice),
        }
    }
}

impl<T: Timing> Eq for G1Projective<T> {}
impl<T: Timing> PartialEq for G1Projective<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match T::VAR {
            true => self.eq_vartime(other),
            false => bool::from(self.ct_eq(other)),
        }
    }
}

impl<'a, T: Timing> Neg for &'a G1Projective<T> {
    type Output = G1Projective<T>;

    #[inline]
    fn neg(self) -> G1Projective<T> {
        (*self).neg()
    }
}

impl<T: Timing> Neg for G1Projective<T> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        self.neg()
    }
}

impl<'a, 'b, T: Timing> Add<&'b G1Projective<T>> for &'a G1Projective<T> {
    type Output = G1Projective<T>;

    #[inline]
    fn add(self, rhs: &'b G1Projective<T>) -> Self::Output {
        (*self).add(rhs)
    }
}

impl<'a, 'b, T: Timing> Sub<&'b G1Projective<T>> for &'a G1Projective<T> {
    type Output = G1Projective<T>;

    #[inline]
    fn sub(self, rhs: &'b G1Projective<T>) -> Self::Output {
        self + (-rhs)
    }
}

impl_binops_additive!{
    {T: Timing}
    {}
    {G1Projective<T>}
    {G1Projective<T>}
}
