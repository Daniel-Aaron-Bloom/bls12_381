//! This module provides an implementation of the BLS12-381 scalar field $\mathbb{F}_q$
//! where `q = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001`

use core::borrow::Borrow;
use core::fmt;
use core::ops::{Add, Mul, MulAssign, Neg, Sub};
use rand_core::RngCore;

use ff::{Field, PrimeField};
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

#[cfg(feature = "bits")]
use ff::{FieldBits, PrimeFieldBits};

use crate::util::{adc, mac, sbb, borrowing_sub, slc, OtherMag, Mag, Never, NonZero, DoubleOp, Ops, copy_bytes};

use self::wide::{square_wide, montgomery_reduce_wide, mul_wide};

mod wide;

#[inline]
const fn negate(v: &[u64; 4], modulus: &[u64; 4]) -> [u64; 4] {
    let (d0, borrow) = borrowing_sub(modulus[0], v[0], false);
    let (d1, borrow) = borrowing_sub(modulus[1], v[1], borrow);
    let (d2, borrow) = borrowing_sub(modulus[2], v[2], borrow);
    let (d3, _borrow) = borrowing_sub(modulus[3], v[3], borrow);

    if cfg!(debug_assertions) && _borrow {
        panic!("borrow != 0");
    }
    
    [d0, d1, d2, d3]
}

#[inline]
const fn add(lhs: &[u64; 4], rhs: &[u64; 4]) -> ([u64; 4], bool) {
    let (d0, carry) = adc(lhs[0], rhs[0], 0);
    let (d1, carry) = adc(lhs[1], rhs[1], carry);
    let (d2, carry) = adc(lhs[2], rhs[2], carry);
    let (d3, carry) = adc(lhs[3], rhs[3], carry);

    ([d0, d1, d2, d3], carry != 0)
}

pub const fn sub_c(lhs: &[u64; 4], rhs: &[u64; 4]) -> ([u64; 4], bool) {
    let (r0, borrow) = borrowing_sub(lhs[0], rhs[0], false);
    let (r1, borrow) = borrowing_sub(lhs[1], rhs[1], borrow);
    let (r2, borrow) = borrowing_sub(lhs[2], rhs[2], borrow);
    let (r3, borrow) = borrowing_sub(lhs[3], rhs[3], borrow);
    ([r0, r1, r2, r3], borrow)
}

#[inline]
const fn sub<const VARTIME: bool>(lhs: &[u64; 4], rhs: &[u64; 4], mut modulus: [u64; 4]) -> [u64; 4] {
    let (v, borrow) = sub_c(lhs, rhs);

    match VARTIME {
        true if borrow => add(&v, &modulus).0,
        true => v,
        false => {
            // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
            // borrow = 0x000...000. Thus, we use it as a mask!
            let borrow = -(borrow as i64) as u64;
            modulus[0] &= borrow;
            modulus[1] &= borrow;
            modulus[2] &= borrow;
            modulus[3] &= borrow;
            add(&v, &modulus).0
        }
    }
}
#[inline]
const fn double(v: &[u64; 4], pow: u32) -> ([u64; 4], bool) {
    let (d0, carry) = slc(v[0], pow, 0);
    let (d1, carry) = slc(v[1], pow, carry);
    let (d2, carry) = slc(v[2], pow, carry);
    let (d3, carry) = slc(v[3], pow, carry);
    
    ([d0, d1, d2, d3], carry != 0)
}

#[inline]
const fn montgomery_reduce<const MAGNITUDE: usize, const VARTIME: bool>(lhs: &[u64; 4]) -> [u64; 4] {
    let mut new = [0; 8];
    new[0] = lhs[0];
    new[1] = lhs[1];
    new[2] = lhs[2];
    new[3] = lhs[3];
    let (mut v, msb) = wide::montgomery_reduce_wide(&new);
    if MAGNITUDE > 0 {
        v = subtract_p::<VARTIME>(msb, &v, &MODULUS.0)
    }
    v
}

#[inline]
const fn subtract_p<const VARTIME: bool>(msb: bool, v: &[u64; 4], modulus: &[u64; 4]) -> [u64; 4] {
    let (r0, borrow) = borrowing_sub(v[0], modulus[0], false);
    let (r1, borrow) = borrowing_sub(v[1], modulus[1], borrow);
    let (r2, borrow) = borrowing_sub(v[2], modulus[2], borrow);
    let (r3, borrow) = borrowing_sub(v[3], modulus[3], borrow);

    match VARTIME {
        true if borrow > msb => *v,
        true => [r0, r1, r2, r3],
        false => {
            // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
            // borrow = 0x000...000. Thus, we use it as a mask!
            let borrow = -(borrow as i64) as u64;
            [
                (v[0] & borrow) | (r0 & !borrow),
                (v[1] & borrow) | (r1 & !borrow),
                (v[2] & borrow) | (r2 & !borrow),
                (v[3] & borrow) | (r3 & !borrow),
            ]
        }
    }
}

/// Represents an element of the scalar field $\mathbb{F}_q$ of the BLS12-381 elliptic
/// curve construction.
// The internal representation of this type is four 64-bit unsigned
// integers in little-endian order. `Scalar` values are always in
// Montgomery form; i.e., Scalar(a) = aR mod q, with R = 2^256.
#[derive(Clone, Copy, Eq)]
pub struct Scalar<const MAGNITUDE: usize = 0, const VARTIME: bool = false>(pub(crate) [u64; 4]);


impl<const MAGNITUDE: usize, const VARTIME: bool> OtherMag for Scalar<MAGNITUDE, VARTIME> {
    const MAGNITUDE: usize = MAGNITUDE;
    type Mag<const MAG2: usize> = Scalar<MAG2, VARTIME>;
}

impl<const VARTIME: bool> Mag<1, [u64; 4]> for Scalar<0, VARTIME> {
    type Prev = Never;
    type Next = Scalar<1, VARTIME>;

    /// A multiple of the prime that is larger than this element could be (p).
    const MODULUS: [u64; 4] = MODULUS.0;

    #[inline(always)]
    fn make([v]: [[u64; 4]; 1]) -> Self {
        Self(v)
    }
    #[inline(always)]
    fn data(&self) -> [&[u64; 4]; 1] {
        [&self.0]
    }
    #[inline(always)]
    fn negate(&self) -> Self {
        self.neg()
    }
}

impl<const VARTIME: bool> Mag<1, [u64; 4]> for Scalar<1, VARTIME> {
    type Prev = Scalar<0, VARTIME>;
    type Next = Never;

    /// A multiple of the prime that is larger than this element could be (p).
    const MODULUS: [u64; 4] = add(&Self::Prev::MODULUS, &MODULUS.0).0;

    #[inline(always)]
    fn make([v]: [[u64; 4]; 1]) -> Self {
        Self(v)
    }
    #[inline(always)]
    fn data(&self) -> [&[u64; 4]; 1] {
        [&self.0]
    }
    #[inline(always)]
    fn negate(&self) -> Self {
        self.neg()
    }

}
impl<const VARTIME: bool> NonZero for Scalar<1, VARTIME> {}

impl<const MAG2: usize, const VARTIME: bool> Ops<1, [u64; 4], Scalar<MAG2, VARTIME>> for Scalar<0, VARTIME>
where
    Scalar<MAG2, VARTIME>: Mag<1, [u64; 4]>,
{
    type OpOut = <Scalar<MAG2, VARTIME> as Mag<1, [u64; 4]>>::Next;
    #[inline(always)]
    fn add(lhs: &Self, rhs: &Scalar<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([add(&lhs.0, &rhs.0).0])
    }
    #[inline(always)]
    fn sub(lhs: &Self, rhs: &Scalar<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([sub::<VARTIME>(&lhs.0, &rhs.0, <Self::OpOut>::MODULUS)])
    }
}

impl<const MAG1: usize, const MAG2: usize, const VARTIME: bool> Ops<1, [u64; 4], Scalar<MAG2, VARTIME>> for Scalar<MAG1, VARTIME>
where
    Scalar<MAG1, VARTIME>: Mag<1, [u64; 4]> + NonZero,
    <Scalar<MAG1, VARTIME> as Mag<1, [u64; 4]>>::Prev: Ops<1, [u64; 4], Scalar<MAG2, VARTIME>>,
    Scalar<MAG2, VARTIME>: Mag<1, [u64; 4]>,
{
    type OpOut =
        <<<Scalar<MAG1, VARTIME> as Mag<1, [u64; 4]>>::Prev as Ops<1, [u64; 4], Scalar<MAG2, VARTIME>>>::OpOut as Mag<1, [u64; 4]>>::Next;
    #[inline(always)]
    fn add(lhs: &Self, rhs: &Scalar<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([add(lhs.data()[0], rhs.data()[0]).0])
    }
    #[inline(always)]
    fn sub(lhs: &Self, rhs: &Scalar<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([sub::<VARTIME>(&lhs.0, &rhs.data()[0], <Self::OpOut>::MODULUS)])
    }
}

macro_rules! impl_double {
    ($pow:literal: $($($ua:literal),+ $(,)?)?) => {$($(
impl<const VARTIME: bool> DoubleOp<$pow> for Scalar<$ua, VARTIME> {
    type DoubleOut = Scalar<{($ua+1)*(1<<($pow+1))-1}, VARTIME>;
    fn double(lhs: &Self) -> Self::DoubleOut {
        Scalar(double(&lhs.0, $pow+1).0)
    }
}
    )+)?};
}
impl_double!{0: 0}

impl<const MAGNITUDE: usize, const VARTIME: bool> fmt::Debug for Scalar<MAGNITUDE, VARTIME> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tmp = self.to_bytes();
        write!(f, "0x")?;
        for &b in tmp.iter().rev() {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> fmt::Display for Scalar<MAGNITUDE, VARTIME> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> From<u64> for Scalar<MAGNITUDE, VARTIME> {
    fn from(val: u64) -> Self {
        Self([val, 0, 0, 0]).mul(&Self(R2.0))
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> ConstantTimeEq for Scalar<MAGNITUDE, VARTIME> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0[0].ct_eq(&other.0[0])
            & self.0[1].ct_eq(&other.0[1])
            & self.0[2].ct_eq(&other.0[2])
            & self.0[3].ct_eq(&other.0[3])
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> PartialEq for Scalar<MAGNITUDE, VARTIME> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match VARTIME {
            true => self.0 == other.0,
            false => bool::from(self.ct_eq(other)),
        }
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> ConditionallySelectable for Scalar<MAGNITUDE, VARTIME> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Scalar([
            u64::conditional_select(&a.0[0], &b.0[0], choice),
            u64::conditional_select(&a.0[1], &b.0[1], choice),
            u64::conditional_select(&a.0[2], &b.0[2], choice),
            u64::conditional_select(&a.0[3], &b.0[3], choice),
        ])
    }
}

/// Constant representing the modulus
/// q = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
const MODULUS: Scalar = Scalar([
    0xffff_ffff_0000_0001,
    0x53bd_a402_fffe_5bfe,
    0x3339_d808_09a1_d805,
    0x73ed_a753_299d_7d48,
]);

/// The modulus as u32 limbs.
#[cfg(all(feature = "bits", not(target_pointer_width = "64")))]
const MODULUS_LIMBS_32: [u32; 8] = [
    0x0000_0001,
    0xffff_ffff,
    0xfffe_5bfe,
    0x53bd_a402,
    0x09a1_d805,
    0x3339_d808,
    0x299d_7d48,
    0x73ed_a753,
];

// The number of bits needed to represent the modulus.
const MODULUS_BITS: u32 = 255;

// GENERATOR = 7 (multiplicative generator of r-1 order, that is also quadratic nonresidue)
const GENERATOR: Scalar = Scalar([
    0x0000_000e_ffff_fff1,
    0x17e3_63d3_0018_9c0f,
    0xff9c_5787_6f84_57b0,
    0x3513_3220_8fc5_a8c4,
]);

impl<'a, const MAGNITUDE: usize, const VARTIME: bool> Neg for &'a Scalar<MAGNITUDE, VARTIME> {
    type Output = Scalar<MAGNITUDE, VARTIME>;

    #[inline]
    fn neg(self) -> Scalar<MAGNITUDE, VARTIME> {
        self.neg()
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> Neg for Scalar<MAGNITUDE, VARTIME> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        -&self
    }
}

impl<'a, 'b, const MAGNITUDE: usize, const VARTIME: bool> Sub<&'b Scalar<MAGNITUDE, VARTIME>> for &'a Scalar<MAGNITUDE, VARTIME> {
    type Output = Scalar<MAGNITUDE, VARTIME>;

    #[inline]
    fn sub(self, rhs: &'b Scalar<MAGNITUDE, VARTIME>) -> Scalar<MAGNITUDE, VARTIME> {
        self.sub(rhs)
    }
}

impl<'a, 'b, const MAGNITUDE: usize, const VARTIME: bool> Add<&'b Scalar<MAGNITUDE, VARTIME>> for &'a Scalar<MAGNITUDE, VARTIME> {
    type Output = Scalar<MAGNITUDE, VARTIME>;

    #[inline]
    fn add(self, rhs: &'b Scalar<MAGNITUDE, VARTIME>) -> Scalar<MAGNITUDE, VARTIME> {
        self.add(rhs)
    }
}

impl<'a, 'b, const MAGNITUDE: usize, const VARTIME: bool> Mul<&'b Scalar<MAGNITUDE, VARTIME>> for &'a Scalar<MAGNITUDE, VARTIME> {
    type Output = Scalar<MAGNITUDE, VARTIME>;

    #[inline]
    fn mul(self, rhs: &'b Scalar<MAGNITUDE, VARTIME>) -> Scalar<MAGNITUDE, VARTIME> {
        self.mul(rhs)
    }
}

impl_binops_additive!{
    {const VARTIME: bool}
    {}
    {Scalar<0, VARTIME>}
    {Scalar<0, VARTIME>}
}
impl_binops_multiplicative!{
    {const VARTIME: bool}
    {}
    {Scalar<0, VARTIME>}
    {Scalar<0, VARTIME>}
}

/// INV = -(q^{-1} mod 2^64) mod 2^64
const INV: u64 = 0xffff_fffe_ffff_ffff;

/// R = 2^256 mod q
const R: Scalar = Scalar([
    0x0000_0001_ffff_fffe,
    0x5884_b7fa_0003_4802,
    0x998c_4fef_ecbc_4ff5,
    0x1824_b159_acc5_056f,
]);

/// R^2 = 2^512 mod q
const R2: Scalar = Scalar([
    0xc999_e990_f3f2_9c6d,
    0x2b6c_edcb_8792_5c23,
    0x05d3_1496_7254_398f,
    0x0748_d9d9_9f59_ff11,
]);

/// R^3 = 2^768 mod q
const R3: Scalar = Scalar([
    0xc62c_1807_439b_73af,
    0x1b3e_0d18_8cf0_6990,
    0x73d1_3c71_c7b5_f418,
    0x6e2a_5bb9_c8db_33e9,
]);

// 2^S * t = MODULUS - 1 with t odd
const S: u32 = 32;

/// GENERATOR^t where t * 2^s + 1 = q
/// with t odd. In other words, this
/// is a 2^s root of unity.
///
/// `GENERATOR = 7 mod q` is a generator
/// of the q - 1 order multiplicative
/// subgroup.
const ROOT_OF_UNITY: Scalar = Scalar([
    0xb9b5_8d8c_5f0e_466a,
    0x5b1b_4c80_1819_d7ec,
    0x0af5_3ae3_52a3_1e64,
    0x5bf3_adda_19e9_b27b,
]);

impl<const MAGNITUDE: usize, const VARTIME: bool> Default for Scalar<MAGNITUDE, VARTIME> {
    #[inline]
    fn default() -> Self {
        Self::zero()
    }
}

#[cfg(feature = "zeroize")]
impl<const MAGNITUDE: usize, const VARTIME: bool> zeroize::DefaultIsZeroes for Scalar<MAGNITUDE, VARTIME> {}

impl<const MAGNITUDE: usize, const VARTIME: bool> Scalar<MAGNITUDE, VARTIME> {
    /// Returns zero, the additive identity.
    #[inline]
    pub const fn zero() -> Self {
        Scalar([0, 0, 0, 0])
    }

    /// Returns one, the multiplicative identity.
    #[inline]
    pub const fn one() -> Self {
        Self(R.0)
    }

    /// Selects between `f` and `t` based on `b`
    pub const fn select(f: Self, t: Self, b: bool) -> Self {
        match VARTIME {
            true if b => t,
            true => f,
            false => {
                let b = -(b as i64) as u64;
                Self([
                    (t.0[0] & b) | (f.0[0] & !b),
                    (t.0[1] & b) | (f.0[1] & !b),
                    (t.0[2] & b) | (f.0[2] & !b),
                    (t.0[3] & b) | (f.0[3] & !b),
                ])
            }
        }
    }

    /// An integer `s` satisfying the equation `2^s * t = modulus - 1` with `t` odd.
    ///
    /// This is the number of leading zero bits in the little-endian bit representation of
    /// `modulus - 1`.
    pub const S: u32 = S;

    /// Returns the `2^S` root of unity.
    pub const fn root_of_unity() -> Self {
        Self(ROOT_OF_UNITY.0)
    }

    /// Returns the `2^bits` root of unity.
    pub const fn omega(bits: u32) -> Self {
        // The pairing-friendly curve may not be able to support
        // large enough (radix2) evaluation domains.
        if bits >= Self::S {
            panic!("unsupported root of unity")
        }

        // Compute omega, the 2^exp primitive root of unity
        Self::root_of_unity().pow_vartime(&[1 << (Self::S - bits), 0, 0, 0])
    }

    /// Adjusts the `VARTIME` setting
    #[inline]
    pub const fn vartime<const VARTIME2: bool>(self) -> Scalar<MAGNITUDE, VARTIME2> {
        Scalar(self.0)
    }

    #[inline]
    /// Returns true if equal
    pub const fn eq_vartime(&self, rhs: &Self) -> bool {
        self.0[0] == rhs.0[0]
            && self.0[1] == rhs.0[1]
            && self.0[2] == rhs.0[2]
            && self.0[3] == rhs.0[3]
    }

    #[inline]
    /// Returns a choice which is true if `self` is zero
    pub fn is_zero(&self) -> Choice {
        self.ct_eq(&Self::zero())
    }

    #[inline]
    /// Returns a `true` if `self` is zero
    pub const fn is_zero_vartime(&self) -> bool {
        self.eq_vartime(&Self::zero())
    }

    #[inline(always)]
    pub(crate) const fn montgomery_reduce(&self) -> [u64; 4] {
        montgomery_reduce::<MAGNITUDE, VARTIME>(&self.0)
    }

    /// Converts an element of `Scalar` into a byte representation in
    /// little-endian byte order.
    pub const fn to_bytes(&self) -> [u8; 32] {
        // Turn into canonical form by computing
        // (a.R) / R = a
        let tmp = self.montgomery_reduce();

        let res = copy_bytes([0; 32], 0, tmp[0].to_le_bytes());
        let res = copy_bytes(res, 8, tmp[1].to_le_bytes());
        let res = copy_bytes(res, 16, tmp[2].to_le_bytes());
        let res = copy_bytes(res, 24, tmp[3].to_le_bytes());

        res
    }

    /// Negates `self`.
    #[inline]
    pub const fn neg(&self) -> Self {
        match VARTIME {
            true if self.is_zero_vartime() => *self,
            true => Self(negate(&self.0, &MODULUS.0)),
            false => {
                // Let's use a mask if `self` was zero, which would mean
                // the result of the subtraction is p.
                let mask = (((self.0[0] | self.0[1] | self.0[2] | self.0[3]) == 0)
                as u64)
                .wrapping_sub(1);

                let v = negate(&self.0, &MODULUS.0);
                Self([
                    v[0] & mask,
                    v[1] & mask,
                    v[2] & mask,
                    v[3] & mask,
                ])
            }
        }
    }

    /// Adds `rhs` to `self`, returning the result.
    #[inline]
    pub const fn add(&self, rhs: &Self) -> Self {
        let (v, carry) = add(&self.0, &rhs.0);

        // Attempt to subtract the modulus, to ensure the value
        // is smaller than the modulus.
        Self(subtract_p::<VARTIME>(carry, &v, &MODULUS.0))
    }

    /// Subtracts `rhs` from `self`, returning the result.
    #[inline]
    pub const fn sub(&self, rhs: &Self) -> Self {
        Self(sub::<VARTIME>(&self.0, &rhs.0, MODULUS.0))
    }

    /// Doubles this field element.
    #[inline]
    pub const fn double(&self) -> Self {
        let (v, carry) = double(&self.0, 1);

        // Attempt to subtract the modulus, to ensure the value
        // is smaller than the modulus.
        Self(subtract_p::<VARTIME>(carry, &v, &MODULUS.0))
    }

    /// Squares this element.
    #[inline]
    pub const fn square(&self) -> Self {
        let mut v = montgomery_reduce_wide(&square_wide(&self.0)).0;
        
        // $Solve[b=((m*p)^2 + 2^256*p - p)/2^256/p && m = 1 && p = 52435875175126190479447740508185965837690552500527637822603658699938581184513, b]$
        // We can see that `montgomery_reduce_wide` will produce results with an upper bound of $p + 0.45285 * m*p$
        // This means we actually only have to reduce the item in two cases
        match MAGNITUDE {
            0 => v = subtract_p::<VARTIME>(false, &v, &<Scalar<0, false> as Mag<1, _>>::MODULUS),
            1 => v = subtract_p::<VARTIME>(false, &v, &<Scalar<1, false> as Mag<1, _>>::MODULUS),
            _ => {},
        }
        Self(v)
    }

    /// Multiplies `rhs` by `self`, returning the result.
    #[inline]
    pub const fn mul(&self, rhs: &Self) -> Self {
        let mut v = montgomery_reduce_wide(&mul_wide(&self.0, &rhs.0)).0;
        
        // $Solve[b=((m*p)^2 + 2^256*p - p)/2^256/p && m = 1 && p = 52435875175126190479447740508185965837690552500527637822603658699938581184513, b]$
        // We can see that `montgomery_reduce_wide` will produce results with an upper bound of $p + 0.45285 * m*p$
        // This means we actually only have to reduce the item in two cases
        match MAGNITUDE {
            0 => v = subtract_p::<VARTIME>(false, &v, &<Scalar<0, false> as Mag<1, _>>::MODULUS),
            1 => v = subtract_p::<VARTIME>(false, &v, &<Scalar<1, false> as Mag<1, _>>::MODULUS),
            _ => {},
        }
        Self(v)
    }

    /// Exponentiates `self` by `by`, where `by` is a
    /// little-endian order integer exponent.
    pub fn pow(&self, by: &[u64; 4]) -> Self {
        let mut res = Self::one();
        for e in by.iter().rev() {
            for i in (0..64).rev() {
                res = res.square();
                let tmp = res.mul(self);
                res.conditional_assign(&tmp, (((*e >> i) & 0x1) as u8).into());
            }
        }
        res
    }

    /// Exponentiates `self` by `by`, where `by` is a
    /// little-endian order integer exponent.
    ///
    /// **This operation is variable time with respect
    /// to the exponent.** If the exponent is fixed,
    /// this operation is effectively constant time.
    pub const fn pow_vartime(&self, by: &[u64; 4]) -> Self {
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

    /// Attempts to convert a little-endian byte representation of
    /// a scalar into a `Scalar`, failing if the input is not canonical.
    pub fn from_bytes(bytes: &[u8; 32]) -> CtOption<Self> {
        let mut tmp = Self([0, 0, 0, 0]);

        tmp.0[0] = u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[0..8]).unwrap());
        tmp.0[1] = u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[8..16]).unwrap());
        tmp.0[2] = u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[16..24]).unwrap());
        tmp.0[3] = u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[24..32]).unwrap());

        // Try to subtract the modulus
        let (_, borrow) = sbb(tmp.0[0], MODULUS.0[0], 0);
        let (_, borrow) = sbb(tmp.0[1], MODULUS.0[1], borrow);
        let (_, borrow) = sbb(tmp.0[2], MODULUS.0[2], borrow);
        let (_, borrow) = sbb(tmp.0[3], MODULUS.0[3], borrow);

        // If the element is smaller than MODULUS then the
        // subtraction will underflow, producing a borrow value
        // of 0xffff...ffff. Otherwise, it'll be zero.
        let is_some = (borrow as u8) & 1;

        // Convert to Montgomery form by computing
        // (a.R^0 * R^2) / R = a.R
        tmp = tmp.mul(&Self(R2.0));

        CtOption::new(tmp, Choice::from(is_some))
    }

    /// Converts a 512-bit little endian integer into
    /// a `Scalar` by reducing by the modulus.
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> Self {
        Self::from_u512([
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[0..8]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[8..16]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[16..24]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[24..32]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[32..40]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[40..48]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[48..56]).unwrap()),
            u64::from_le_bytes(<[u8; 8]>::try_from(&bytes[56..64]).unwrap()),
        ])
    }

    const fn from_u512(limbs: [u64; 8]) -> Self {
        // We reduce an arbitrary 512-bit number by decomposing it into two 256-bit digits
        // with the higher bits multiplied by 2^256. Thus, we perform two reductions
        //
        // 1. the lower bits are multiplied by R^2, as normal
        // 2. the upper bits are multiplied by R^2 * 2^256 = R^3
        //
        // and computing their sum in the field. It remains to see that arbitrary 256-bit
        // numbers can be placed into Montgomery form safely using the reduction. The
        // reduction works so long as the product is less than R=2^256 multiplied by
        // the modulus. This holds because for any `c` smaller than the modulus, we have
        // that (2^256 - 1)*c is an acceptable product for the reduction. Therefore, the
        // reduction always works so long as `c` is in the field; in this case it is either the
        // constant `R2` or `R3`.
        let d0 = Self([limbs[0], limbs[1], limbs[2], limbs[3]]);
        let d1 = Self([limbs[4], limbs[5], limbs[6], limbs[7]]);
        // Convert to Montgomery form
        d0.mul(&Self(R2.0)).add(&d1.mul(&Self(R3.0)))
    }

    /// Converts from an integer represented in little endian
    /// into its (congruent) `Scalar` representation.
    pub const fn from_raw(val: [u64; 4]) -> Self {
        (&Scalar(val)).mul(&Self(R2.0))
    }

    /// Computes the square root of this element, if it exists.
    pub fn sqrt(&self) -> CtOption<Self> {
        // Tonelli-Shank's algorithm for q mod 16 = 1
        // https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5)

        // w = self^((t - 1) // 2)
        //   = self^6104339283789297388802252303364915521546564123189034618274734669823
        let w = self.pow_vartime(&[
            0x7fff_2dff_7fff_ffff,
            0x04d0_ec02_a9de_d201,
            0x94ce_bea4_199c_ec04,
            0x0000_0000_39f6_d3a9,
        ]);

        let mut v = S;
        let mut x = self.mul(&w);
        let mut b = x.mul(&w);

        // Initialize z as the 2^S root of unity.
        let mut z = Self(ROOT_OF_UNITY.0);

        for max_v in (1..=S).rev() {
            let mut k = 1;
            let mut tmp = b.square();
            let mut j_less_than_v: Choice = 1.into();

            for j in 2..max_v {
                let tmp_is_one = tmp.ct_eq(&Scalar::one());
                let squared = Scalar::conditional_select(&tmp, &z, tmp_is_one).square();
                tmp = Scalar::conditional_select(&squared, &tmp, tmp_is_one);
                let new_z = Scalar::conditional_select(&z, &squared, tmp_is_one);
                j_less_than_v &= !j.ct_eq(&v);
                k = u32::conditional_select(&j, &k, tmp_is_one);
                z = Scalar::conditional_select(&z, &new_z, j_less_than_v);
            }

            let result = x.mul(&z);
            x = Scalar::conditional_select(&result, &x, b.ct_eq(&Scalar::one()));
            z = z.square();
            b = b.mul(&z);
            v = k;
        }

        CtOption::new(
            x,
            x.square().ct_eq(self), // Only return Some if it's the square root.
        )
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    pub fn invert(&self) -> CtOption<Self> {
        #[inline(always)]
        fn square_assign_multi<const MAGNITUDE: usize, const VARTIME: bool>(n: &mut Scalar<MAGNITUDE, VARTIME>, num_times: usize) {
            for _ in 0..num_times {
                *n = n.square();
            }
        }
        // found using https://github.com/kwantam/addchain
        let mut t0 = self.square();
        let mut t1 = t0.mul(self);
        let mut t16 = t0.square();
        let mut t6 = t16.square();
        let mut t5 = t6.mul(&t0);
        t0 = t6.mul(&t16);
        let mut t12 = t5.mul(&t16);
        let mut t2 = t6.square();
        let mut t7 = t5.mul(&t6);
        let mut t15 = t0.mul(&t5);
        let mut t17 = t12.square();
        t1 = t1.mul(&t17);
        let mut t3 = t7.mul(&t2);
        let t8 = t1.mul(&t17);
        let t4 = t8.mul(&t2);
        let t9 = t8.mul(&t7);
        t7 = t4.mul(&t5);
        let t11 = t4.mul(&t17);
        t5 = t9.mul(&t17);
        let t14 = t7.mul(&t15);
        let t13 = t11.mul(&t12);
        t12 = t11.mul(&t17);
        t15 = t15.mul(&t12);
        t16 = t16.mul(&t15);
        t3 = t3.mul(&t16);
        t17 = t17.mul(&t3);
        t0 = t0.mul(&t17);
        t6 = t6.mul(&t0);
        t2 = t2.mul(&t6);
        square_assign_multi(&mut t0, 8);
        t0 = t0.mul(&t17);
        square_assign_multi(&mut t0, 9);
        t0 = t0.mul(&t16);
        square_assign_multi(&mut t0, 9);
        t0 = t0.mul(&t15);
        square_assign_multi(&mut t0, 9);
        t0 = t0.mul(&t15);
        square_assign_multi(&mut t0, 7);
        t0 = t0.mul(&t14);
        square_assign_multi(&mut t0, 7);
        t0 = t0.mul(&t13);
        square_assign_multi(&mut t0, 10);
        t0 = t0.mul(&t12);
        square_assign_multi(&mut t0, 9);
        t0 = t0.mul(&t11);
        square_assign_multi(&mut t0, 8);
        t0 = t0.mul(&t8);
        square_assign_multi(&mut t0, 8);
        t0 = t0.mul(self);
        square_assign_multi(&mut t0, 14);
        t0 = t0.mul(&t9);
        square_assign_multi(&mut t0, 10);
        t0 = t0.mul(&t8);
        square_assign_multi(&mut t0, 15);
        t0 = t0.mul(&t7);
        square_assign_multi(&mut t0, 10);
        t0 = t0.mul(&t6);
        square_assign_multi(&mut t0, 8);
        t0 = t0.mul(&t5);
        square_assign_multi(&mut t0, 16);
        t0 = t0.mul(&t3);
        square_assign_multi(&mut t0, 8);
        t0 = t0.mul(&t2);
        square_assign_multi(&mut t0, 7);
        t0 = t0.mul(&t4);
        square_assign_multi(&mut t0, 9);
        t0 = t0.mul(&t2);
        square_assign_multi(&mut t0, 8);
        t0 = t0.mul(&t3);
        square_assign_multi(&mut t0, 8);
        t0 = t0.mul(&t2);
        square_assign_multi(&mut t0, 8);
        t0 = t0.mul(&t2);
        square_assign_multi(&mut t0, 8);
        t0 = t0.mul(&t2);
        square_assign_multi(&mut t0, 8);
        t0 = t0.mul(&t3);
        square_assign_multi(&mut t0, 8);
        t0 = t0.mul(&t2);
        square_assign_multi(&mut t0, 8);
        t0 = t0.mul(&t2);
        square_assign_multi(&mut t0, 5);
        t0 = t0.mul(&t1);
        square_assign_multi(&mut t0, 5);
        t0 = t0.mul(&t1);

        CtOption::new(t0, !self.ct_eq(&Self::zero()))
    }

    /// Inverts a batch of `Scalar` elements into `G1Affine` elements.
    /// function will panic if `p.len() != q.len()`. Does not alter 'q[i]` when `p[i].is_zero()`.
    pub fn invert_batch<P>(p: P, q: &mut [Self])
    where P: DoubleEndedIterator+Clone, P::Item: Borrow<Self>{

        let mut acc = Self::one();
        for (p, q) in p.clone().zip(q.iter_mut()) {
            let p = p.borrow();
            *q = Scalar::conditional_select(&acc, q, p.is_zero());
            acc = Scalar::conditional_select(&acc.mul(p), &acc, p.is_zero());
        }

        // This is the inverse, as all z-coordinates are nonzero and the ones
        // that are not are skipped.
        acc = acc.invert().unwrap();

        for (p, q) in p.rev().zip(q.iter_mut().rev()) {
            let p = p.borrow();

            // Compute = 1/z
            *q = Scalar::conditional_select(&acc.mul(q), q, p.is_zero());

            // Cancel out z-coordinate in denominator of `acc`
            acc = Scalar::conditional_select(&acc.mul(p), &acc, p.is_zero());
        }
    }
}

impl From<Scalar> for [u8; 32] {
    fn from(value: Scalar) -> [u8; 32] {
        value.to_bytes()
    }
}

impl<'a> From<&'a Scalar> for [u8; 32] {
    fn from(value: &'a Scalar) -> [u8; 32] {
        value.to_bytes()
    }
}

impl<const VARTIME: bool> Field for Scalar<0, VARTIME> {
    fn random(mut rng: impl RngCore) -> Self {
        let mut buf = [0; 64];
        rng.fill_bytes(&mut buf);
        Self::from_bytes_wide(&buf)
    }

    fn zero() -> Self {
        Self::zero()
    }

    fn one() -> Self {
        Self::one()
    }

    #[must_use]
    fn square(&self) -> Self {
        self.square()
    }

    #[must_use]
    fn double(&self) -> Self {
        self.double()
    }

    fn invert(&self) -> CtOption<Self> {
        self.invert()
    }

    fn sqrt(&self) -> CtOption<Self> {
        self.sqrt()
    }

    fn is_zero_vartime(&self) -> bool {
        self.0 == Self::zero().0
    }
}

impl<const VARTIME: bool> PrimeField for Scalar<0, VARTIME> {
    type Repr = [u8; 32];

    fn from_repr(r: Self::Repr) -> CtOption<Self> {
        Self::from_bytes(&r)
    }

    fn to_repr(&self) -> Self::Repr {
        self.to_bytes()
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.to_bytes()[0] & 1)
    }

    const NUM_BITS: u32 = MODULUS_BITS;
    const CAPACITY: u32 = Self::NUM_BITS - 1;

    fn multiplicative_generator() -> Self {
        GENERATOR.vartime()
    }

    const S: u32 = S;

    fn root_of_unity() -> Self {
        ROOT_OF_UNITY.vartime()
    }
}

#[cfg(all(feature = "bits", not(target_pointer_width = "64")))]
type ReprBits = [u32; 8];

#[cfg(all(feature = "bits", target_pointer_width = "64"))]
type ReprBits = [u64; 4];

#[cfg(feature = "bits")]
impl<const VARTIME: bool> PrimeFieldBits for Scalar<0, VARTIME> {
    type ReprBits = ReprBits;

    fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
        let bytes = self.to_bytes();

        #[cfg(not(target_pointer_width = "64"))]
        let limbs = [
            u32::from_le_bytes(be_bytes_to_u64[0..4].try_into().unwrap()),
            u32::from_le_bytes(be_bytes_to_u64[4..8].try_into().unwrap()),
            u32::from_le_bytes(be_bytes_to_u64[8..12].try_into().unwrap()),
            u32::from_le_bytes(be_bytes_to_u64[12..16].try_into().unwrap()),
            u32::from_le_bytes(be_bytes_to_u64[16..20].try_into().unwrap()),
            u32::from_le_bytes(be_bytes_to_u64[20..24].try_into().unwrap()),
            u32::from_le_bytes(be_bytes_to_u64[24..28].try_into().unwrap()),
            u32::from_le_bytes(be_bytes_to_u64[28..32].try_into().unwrap()),
        ];

        #[cfg(target_pointer_width = "64")]
        let limbs = [
            u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
        ];

        FieldBits::new(limbs)
    }

    fn char_le_bits() -> FieldBits<Self::ReprBits> {
        #[cfg(not(target_pointer_width = "64"))]
        {
            FieldBits::new(MODULUS_LIMBS_32)
        }

        #[cfg(target_pointer_width = "64")]
        FieldBits::new(MODULUS.0)
    }
}

impl<T, const MAGNITUDE: usize, const VARTIME: bool> core::iter::Sum<T> for Scalar<MAGNITUDE, VARTIME>
where
    T: core::borrow::Borrow<Scalar<MAGNITUDE, VARTIME>>,
{
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = T>,
    {
        iter.fold(Self::zero(), |acc, item| acc.add(item.borrow()))
    }
}

#[test]
fn test_inv() {
    // Compute -(q^{-1} mod 2^64) mod 2^64 by exponentiating
    // by totient(2**64) - 1

    let mut inv = 1u64;
    for _ in 0..63 {
        inv = inv.wrapping_mul(inv);
        inv = inv.wrapping_mul(MODULUS.0[0]);
    }
    inv = inv.wrapping_neg();

    assert_eq!(inv, INV);
}

#[cfg(feature = "std")]
#[test]
fn test_debug() {
    assert_eq!(
        format!("{:?}", Scalar::zero()),
        "0x0000000000000000000000000000000000000000000000000000000000000000"
    );
    assert_eq!(
        format!("{:?}", Scalar::one()),
        "0x0000000000000000000000000000000000000000000000000000000000000001"
    );
    assert_eq!(
        format!("{:?}", R2),
        "0x1824b159acc5056f998c4fefecbc4ff55884b7fa0003480200000001fffffffe"
    );
}

#[test]
fn test_equality() {
    assert_eq!(Scalar::<0, false>::zero(), Scalar::zero());
    assert_eq!(Scalar::<0, false>::one(), Scalar::one());
    assert_eq!(R2, R2);

    assert!(Scalar::<0, false>::zero() != Scalar::one());
    assert!(Scalar::<0, false>::one() != R2);
}

#[test]
fn test_to_bytes() {
    assert_eq!(
        Scalar::<0, false>::zero().to_bytes(),
        [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0
        ]
    );

    assert_eq!(
        Scalar::<0, false>::one().to_bytes(),
        [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0
        ]
    );

    assert_eq!(
        R2.to_bytes(),
        [
            254, 255, 255, 255, 1, 0, 0, 0, 2, 72, 3, 0, 250, 183, 132, 88, 245, 79, 188, 236, 239,
            79, 140, 153, 111, 5, 197, 172, 89, 177, 36, 24
        ]
    );

    assert_eq!(
        (-&Scalar::<0, false>::one()).to_bytes(),
        [
            0, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8,
            216, 57, 51, 72, 125, 157, 41, 83, 167, 237, 115
        ]
    );
}

#[test]
fn test_from_bytes() {
    assert_eq!(
        Scalar::<0, false>::from_bytes(&[
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0
        ])
        .unwrap(),
        Scalar::zero()
    );

    assert_eq!(
        Scalar::<0, false>::from_bytes(&[
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0
        ])
        .unwrap(),
        Scalar::one()
    );

    assert_eq!(
        Scalar::<0, false>::from_bytes(&[
            254, 255, 255, 255, 1, 0, 0, 0, 2, 72, 3, 0, 250, 183, 132, 88, 245, 79, 188, 236, 239,
            79, 140, 153, 111, 5, 197, 172, 89, 177, 36, 24
        ])
        .unwrap(),
        R2
    );

    // -1 should work
    assert!(bool::from(
        Scalar::<0, false>::from_bytes(&[
            0, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8,
            216, 57, 51, 72, 125, 157, 41, 83, 167, 237, 115
        ])
        .is_some()
    ));

    // modulus is invalid
    assert!(bool::from(
        Scalar::<0, false>::from_bytes(&[
            1, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8,
            216, 57, 51, 72, 125, 157, 41, 83, 167, 237, 115
        ])
        .is_none()
    ));

    // Anything larger than the modulus is invalid
    assert!(bool::from(
        Scalar::<0, false>::from_bytes(&[
            2, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8,
            216, 57, 51, 72, 125, 157, 41, 83, 167, 237, 115
        ])
        .is_none()
    ));
    assert!(bool::from(
        Scalar::<0, false>::from_bytes(&[
            1, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8,
            216, 58, 51, 72, 125, 157, 41, 83, 167, 237, 115
        ])
        .is_none()
    ));
    assert!(bool::from(
        Scalar::<0, false>::from_bytes(&[
            1, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8,
            216, 57, 51, 72, 125, 157, 41, 83, 167, 237, 116
        ])
        .is_none()
    ));
}

#[test]
fn test_from_u512_zero() {
    assert_eq!(
        Scalar::<0, false>::zero(),
        Scalar::from_u512([
            MODULUS.0[0],
            MODULUS.0[1],
            MODULUS.0[2],
            MODULUS.0[3],
            0,
            0,
            0,
            0
        ])
    );
}

#[test]
fn test_from_u512_r() {
    assert_eq!(R, Scalar::from_u512([1, 0, 0, 0, 0, 0, 0, 0]));
}

#[test]
fn test_from_u512_r2() {
    assert_eq!(R2, Scalar::from_u512([0, 0, 0, 0, 1, 0, 0, 0]));
}

#[test]
fn test_from_u512_max() {
    let max_u64 = 0xffff_ffff_ffff_ffff;
    assert_eq!(
        R3 - R,
        Scalar::from_u512([max_u64, max_u64, max_u64, max_u64, max_u64, max_u64, max_u64, max_u64])
    );
}

#[test]
fn test_from_bytes_wide_r2() {
    assert_eq!(
        R2,
        Scalar::from_bytes_wide(&[
            254, 255, 255, 255, 1, 0, 0, 0, 2, 72, 3, 0, 250, 183, 132, 88, 245, 79, 188, 236, 239,
            79, 140, 153, 111, 5, 197, 172, 89, 177, 36, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ])
    );
}

#[test]
fn test_from_bytes_wide_negative_one() {
    assert_eq!(
        -&Scalar::<0, false>::one(),
        Scalar::from_bytes_wide(&[
            0, 0, 0, 0, 255, 255, 255, 255, 254, 91, 254, 255, 2, 164, 189, 83, 5, 216, 161, 9, 8,
            216, 57, 51, 72, 125, 157, 41, 83, 167, 237, 115, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ])
    );
}

#[test]
fn test_from_bytes_wide_maximum() {
    assert_eq!(
        Scalar::<0, false>([
            0xc62c_1805_439b_73b1,
            0xc2b9_551e_8ced_218e,
            0xda44_ec81_daf9_a422,
            0x5605_aa60_1c16_2e79,
        ]),
        Scalar::from_bytes_wide(&[0xff; 64])
    );
}

#[test]
fn test_zero() {
    assert_eq!(Scalar::<0, false>::zero(), -&Scalar::zero());
    assert_eq!(Scalar::<0, false>::zero(), Scalar::zero() + Scalar::zero());
    assert_eq!(Scalar::<0, false>::zero(), Scalar::zero() - Scalar::zero());
    assert_eq!(Scalar::<0, false>::zero(), Scalar::zero() * Scalar::zero());
}

#[cfg(test)]
const LARGEST: Scalar = Scalar([
    0xffff_ffff_0000_0000,
    0x53bd_a402_fffe_5bfe,
    0x3339_d808_09a1_d805,
    0x73ed_a753_299d_7d48,
]);

#[test]
fn test_addition() {
    let mut tmp = LARGEST;
    tmp += &LARGEST;

    assert_eq!(
        tmp,
        Scalar([
            0xffff_fffe_ffff_ffff,
            0x53bd_a402_fffe_5bfe,
            0x3339_d808_09a1_d805,
            0x73ed_a753_299d_7d48,
        ])
    );

    let mut tmp = LARGEST;
    tmp += &Scalar([1, 0, 0, 0]);

    assert_eq!(tmp, Scalar::zero());
}

#[test]
fn test_negation() {
    let tmp = -&LARGEST;

    assert_eq!(tmp, Scalar([1, 0, 0, 0]));

    let tmp: Scalar = -&Scalar::zero();
    assert_eq!(tmp, Scalar::zero());
    let tmp = -&Scalar([1, 0, 0, 0]);
    assert_eq!(tmp, LARGEST);
}

#[test]
fn test_subtraction() {
    let mut tmp = LARGEST;
    tmp -= &LARGEST;

    assert_eq!(tmp, Scalar::zero());

    let mut tmp = Scalar::zero();
    tmp -= &LARGEST;

    let mut tmp2 = MODULUS;
    tmp2 -= &LARGEST;

    assert_eq!(tmp, tmp2);
}

#[test]
fn test_multiplication() {
    let mut cur = LARGEST;

    for _ in 0..100 {
        let mut tmp = cur;
        tmp *= &cur;

        let mut tmp2 = Scalar::zero();
        for b in cur
            .to_bytes()
            .iter()
            .rev()
            .flat_map(|byte| (0..8).rev().map(move |i| ((byte >> i) & 1u8) == 1u8))
        {
            let tmp3 = tmp2;
            tmp2 += &tmp3;

            if b {
                tmp2 += &cur;
            }
        }

        assert_eq!(tmp, tmp2);

        cur += &LARGEST;
    }
}

#[test]
fn test_squaring() {
    let mut cur = LARGEST;

    for _ in 0..100 {
        let mut tmp = cur;
        tmp = tmp.square();

        let mut tmp2 = Scalar::zero();
        for b in cur
            .to_bytes()
            .iter()
            .rev()
            .flat_map(|byte| (0..8).rev().map(move |i| ((byte >> i) & 1u8) == 1u8))
        {
            let tmp3 = tmp2;
            tmp2 += &tmp3;

            if b {
                tmp2 += &cur;
            }
        }

        assert_eq!(tmp, tmp2);

        cur += &LARGEST;
    }
}

#[test]
fn test_inversion() {
    use rand_core::SeedableRng;
    let mut rng = rand_xorshift::XorShiftRng::from_seed([
        0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
        0xbc, 0xe5,
    ]);

    assert!(bool::from(Scalar::<0, false>::zero().invert().is_none()));
    assert_eq!(Scalar::<0, false>::one().invert().unwrap(), Scalar::one());
    assert_eq!((-&Scalar::<0, false>::one()).invert().unwrap(), -&Scalar::one());

    let mut tmp = R2;

    for _ in 0..100 {
        let mut tmp2 = tmp.invert().unwrap();
        tmp2.mul_assign(&tmp);

        assert_eq!(tmp2, Scalar::one());

        tmp += &R2;
    }
    
    let mut p: [Scalar; 100] = [(); 100].map(|()| Scalar::random(&mut rng));
    p[40] = Scalar::zero();
    let mut q = [Scalar::zero(); 100];
    Scalar::invert_batch(p.iter(), &mut q);

    for (p, q) in p.iter().zip(q.iter()) {
        if p.is_zero_vartime() {
            assert!(q.is_zero_vartime());
        } else {
            assert_eq!(p.mul(q), Scalar::one())
        }
    }
    
}

#[test]
fn test_invert_is_pow() {
    let q_minus_2 = [
        0xffff_fffe_ffff_ffff,
        0x53bd_a402_fffe_5bfe,
        0x3339_d808_09a1_d805,
        0x73ed_a753_299d_7d48,
    ];

    let mut r1 = R;
    let mut r2 = R;
    let mut r3 = R;

    for _ in 0..100 {
        r1 = r1.invert().unwrap();
        r2 = r2.pow_vartime(&q_minus_2);
        r3 = r3.pow(&q_minus_2);

        assert_eq!(r1, r2);
        assert_eq!(r2, r3);
        // Add R so we check something different next time around
        r1 += &R;
        r2 = r1;
        r3 = r1;
    }
}

#[test]
fn test_sqrt() {
    {
        assert_eq!(Scalar::<0, false>::zero().sqrt().unwrap(), Scalar::zero());
    }

    let mut square: Scalar = Scalar([
        0x46cd_85a5_f273_077e,
        0x1d30_c47d_d68f_c735,
        0x77f6_56f6_0bec_a0eb,
        0x494a_a01b_df32_468d,
    ]);

    let mut none_count = 0;

    for _ in 0..100 {
        let square_root = square.sqrt();
        if bool::from(square_root.is_none()) {
            none_count += 1;
        } else {
            assert_eq!(square_root.unwrap() * square_root.unwrap(), square);
        }
        square -= Scalar::one();
    }

    assert_eq!(49, none_count);
}

#[test]
fn test_from_raw() {
    assert_eq!(
        Scalar::<0, false>::from_raw([
            0x0001_ffff_fffd,
            0x5884_b7fa_0003_4802,
            0x998c_4fef_ecbc_4ff5,
            0x1824_b159_acc5_056f,
        ]),
        Scalar::from_raw([0xffff_ffff_ffff_ffff; 4])
    );

    assert_eq!(Scalar::<0, false>::from_raw(MODULUS.0), Scalar::zero());

    assert_eq!(Scalar::from_raw([1, 0, 0, 0]), R);
}

#[test]
fn test_double() {
    let a: Scalar = Scalar::from_raw([
        0x1fff_3231_233f_fffd,
        0x4884_b7fa_0003_4802,
        0x998c_4fef_ecbc_4ff3,
        0x1824_b159_acc5_0562,
    ]);

    assert_eq!(a.double(), a + a);
}

#[cfg(feature = "zeroize")]
#[test]
fn test_zeroize() {
    use zeroize::Zeroize;

    let mut a = Scalar::from_raw([
        0x1fff_3231_233f_fffd,
        0x4884_b7fa_0003_4802,
        0x998c_4fef_ecbc_4ff3,
        0x1824_b159_acc5_0562,
    ]);
    a.zeroize();
    assert!(bool::from(a.is_zero()));
}
