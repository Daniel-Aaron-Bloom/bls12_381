//! This module provides an implementation of the BLS12-381 base field `GF(p)`
//! where `p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab`
#![allow(missing_docs)]

use core::fmt;
use core::marker::PhantomData;
use core::ops::{Add, Mul, MulAssign, Neg, Sub};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

use crate::util::{adc, sbb, borrowing_sub, carrying_add, mac, slc, Mag, DoubleOp, Never, NonZero, MontOp, OtherMag, Ops, FpMagnitude, RawMagnitude, FpMag, MagAdd, MagDouble, MagReduce, MagFp, MagLsh, MagSub, MagSquare, MagFpWide, MagMul, Timing, ConstTime, copy_bytes};

pub mod wide;
use wide::FpWide;

use self::wide::{square_wide, montgomery_reduce_wide, mul_wide, add_wide_c, subtract_p_wide, WIDE_MODS, montgomery_reduce_full, FpAWide};

#[inline(always)]
fn ct_eq(lhs: &[u64; 6], rhs: &[u64; 6]) -> Choice {
    lhs[0].ct_eq(&rhs[0])
        & lhs[1].ct_eq(&rhs[1])
        & lhs[2].ct_eq(&rhs[2])
        & lhs[3].ct_eq(&rhs[3])
        & lhs[4].ct_eq(&rhs[4])
        & lhs[5].ct_eq(&rhs[5])
}

#[inline(always)]
const fn eq_vartime(lhs: &[u64; 6], rhs: &[u64; 6]) -> bool {
    lhs[0] == rhs[0]
        && lhs[1] == rhs[1]
        && lhs[2] == rhs[2]
        && lhs[3] == rhs[3]
        && lhs[4] == rhs[4]
        && lhs[5] == rhs[5]
}

#[inline]
const fn negate(v: &[u64; 6], modulus: &[u64; 6]) -> [u64; 6] {
    let (d0, borrow) = borrowing_sub(modulus[0], v[0], false);
    let (d1, borrow) = borrowing_sub(modulus[1], v[1], borrow);
    let (d2, borrow) = borrowing_sub(modulus[2], v[2], borrow);
    let (d3, borrow) = borrowing_sub(modulus[3], v[3], borrow);
    let (d4, borrow) = borrowing_sub(modulus[4], v[4], borrow);
    let (d5, _borrow) = borrowing_sub(modulus[5], v[5], borrow);

    if cfg!(debug_assertions) && _borrow {
        panic!("borrow != 0");
    }

    [d0, d1, d2, d3, d4, d5]
}

#[inline]
const fn add_c(lhs: &[u64; 6], rhs: &[u64; 6]) -> ([u64; 6], bool) {
    let (d0, carry) = adc(lhs[0], rhs[0], 0);
    let (d1, carry) = adc(lhs[1], rhs[1], carry);
    let (d2, carry) = adc(lhs[2], rhs[2], carry);
    let (d3, carry) = adc(lhs[3], rhs[3], carry);
    let (d4, carry) = adc(lhs[4], rhs[4], carry);
    let (d5, carry) = adc(lhs[5], rhs[5], carry);

    ([d0, d1, d2, d3, d4, d5], carry != 0)
}

#[inline]
const fn add(lhs: &[u64; 6], rhs: &[u64; 6]) -> [u64; 6] {
    let (v, _carry) = add_c(lhs, rhs);

    if cfg!(debug_assertions) && _carry {
        panic!("carry != 0");
    }

    v
}

#[inline]
const fn sub<const VARTIME: bool>(lhs: &[u64; 6], rhs: &[u64; 6], mut modulus: [u64; 6]) -> [u64; 6] {
    let (r0, borrow) = borrowing_sub(lhs[0], rhs[0], false);
    let (r1, borrow) = borrowing_sub(lhs[1], rhs[1], borrow);
    let (r2, borrow) = borrowing_sub(lhs[2], rhs[2], borrow);
    let (r3, borrow) = borrowing_sub(lhs[3], rhs[3], borrow);
    let (r4, borrow) = borrowing_sub(lhs[4], rhs[4], borrow);
    let (r5, borrow) = borrowing_sub(lhs[5], rhs[5], borrow);

    let v = [r0, r1, r2, r3, r4, r5];
    match VARTIME {
        true if borrow => add_c(&v, &modulus).0,
        true => v,
        false => {
            // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
            // borrow = 0x000...000. Thus, we use it as a mask!
            let borrow = -(borrow as i64) as u64;
            modulus[0] &= borrow;
            modulus[1] &= borrow;
            modulus[2] &= borrow;
            modulus[3] &= borrow;
            modulus[4] &= borrow;
            modulus[5] &= borrow;
            add_c(&v, &modulus).0
        }
    }
}

#[inline]
const fn subt<T: Timing>(lhs: &[u64; 6], rhs: &[u64; 6], mut modulus: [u64; 6]) -> [u64; 6] {
    let (r0, borrow) = borrowing_sub(lhs[0], rhs[0], false);
    let (r1, borrow) = borrowing_sub(lhs[1], rhs[1], borrow);
    let (r2, borrow) = borrowing_sub(lhs[2], rhs[2], borrow);
    let (r3, borrow) = borrowing_sub(lhs[3], rhs[3], borrow);
    let (r4, borrow) = borrowing_sub(lhs[4], rhs[4], borrow);
    let (r5, borrow) = borrowing_sub(lhs[5], rhs[5], borrow);

    let v = [r0, r1, r2, r3, r4, r5];
    match T::VAR {
        true if borrow => add_c(&v, &modulus).0,
        true => v,
        false => {
            // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
            // borrow = 0x000...000. Thus, we use it as a mask!
            let borrow = -(borrow as i64) as u64;
            modulus[0] &= borrow;
            modulus[1] &= borrow;
            modulus[2] &= borrow;
            modulus[3] &= borrow;
            modulus[4] &= borrow;
            modulus[5] &= borrow;
            add_c(&v, &modulus).0
        }
    }
}

#[inline]
const fn double_c(v: &[u64; 6], pow: u32) -> ([u64; 6], bool) {
    let (d0, carry) = slc(v[0], pow, 0);
    let (d1, carry) = slc(v[1], pow, carry);
    let (d2, carry) = slc(v[2], pow, carry);
    let (d3, carry) = slc(v[3], pow, carry);
    let (d4, carry) = slc(v[4], pow, carry);
    let (d5, carry) = slc(v[5], pow, carry);

    ([d0, d1, d2, d3, d4, d5], carry != 0)
}

#[inline]
const fn double(v: &[u64; 6], pow: u32) -> [u64; 6] {
    let (v, _carry) = double_c(v, pow);

    if cfg!(debug_assertions) && _carry {
        panic!("carry != 0");
    }

    v
}

#[inline]
const fn subtract_p<const VARTIME: bool>(msb: bool, v: &[u64; 6], modulus: &[u64; 6]) -> [u64; 6] {
    let (r0, borrow) = borrowing_sub(v[0], modulus[0], false);
    let (r1, borrow) = borrowing_sub(v[1], modulus[1], borrow);
    let (r2, borrow) = borrowing_sub(v[2], modulus[2], borrow);
    let (r3, borrow) = borrowing_sub(v[3], modulus[3], borrow);
    let (r4, borrow) = borrowing_sub(v[4], modulus[4], borrow);
    let (r5, borrow) = borrowing_sub(v[5], modulus[5], borrow);

    match VARTIME {
        true if borrow > msb => *v,
        true => [r0, r1, r2, r3, r4, r5],
        false => {
            // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
            // borrow = 0x000...000. Thus, we use it as a mask!
            let borrow = -(borrow as i64 & !msb as i64) as u64;
            [
                (v[0] & borrow) | (r0 & !borrow),
                (v[1] & borrow) | (r1 & !borrow),
                (v[2] & borrow) | (r2 & !borrow),
                (v[3] & borrow) | (r3 & !borrow),
                (v[4] & borrow) | (r4 & !borrow),
                (v[5] & borrow) | (r5 & !borrow),
            ]
        }
    }
}

#[inline]
const fn subtract_pt<T: Timing>(msb: bool, v: &[u64; 6], modulus: &[u64; 6]) -> [u64; 6] {
    let (r0, borrow) = borrowing_sub(v[0], modulus[0], false);
    let (r1, borrow) = borrowing_sub(v[1], modulus[1], borrow);
    let (r2, borrow) = borrowing_sub(v[2], modulus[2], borrow);
    let (r3, borrow) = borrowing_sub(v[3], modulus[3], borrow);
    let (r4, borrow) = borrowing_sub(v[4], modulus[4], borrow);
    let (r5, borrow) = borrowing_sub(v[5], modulus[5], borrow);

    match T::VAR {
        true if borrow > msb => *v,
        true => [r0, r1, r2, r3, r4, r5],
        false => {
            // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
            // borrow = 0x000...000. Thus, we use it as a mask!
            let borrow = -(borrow as i64 & !msb as i64) as u64;
            [
                (v[0] & borrow) | (r0 & !borrow),
                (v[1] & borrow) | (r1 & !borrow),
                (v[2] & borrow) | (r2 & !borrow),
                (v[3] & borrow) | (r3 & !borrow),
                (v[4] & borrow) | (r4 & !borrow),
                (v[5] & borrow) | (r5 & !borrow),
            ]
        }
    }
}

#[inline]
const fn montgomery_reduce<const VARTIME: bool>(magnitude: usize, lhs: &[u64; 6]) -> [u64; 6] {
    let mut new = [0; 12];
    new[0] = lhs[0];
    new[1] = lhs[1];
    new[2] = lhs[2];
    new[3] = lhs[3];
    new[4] = lhs[4];
    new[5] = lhs[5];
    let (mut v, msb) = wide::montgomery_reduce_wide(&new);
    if magnitude > 0 {
        v = subtract_p::<VARTIME>(msb, &v, &MODULUS)
    }
    v
}

#[inline]
const fn montgomery_reducet<T: Timing>(magnitude: usize, lhs: &[u64; 6]) -> [u64; 6] {
    let mut new = [0; 12];
    new[0] = lhs[0];
    new[1] = lhs[1];
    new[2] = lhs[2];
    new[3] = lhs[3];
    new[4] = lhs[4];
    new[5] = lhs[5];
    let (mut v, msb) = wide::montgomery_reduce_wide(&new);
    if magnitude > 0 {
        v = subtract_pt::<T>(msb, &v, &MODULUS)
    }
    v
}

#[inline(always)]
pub const fn reduce_full<const VARTIME: bool>(mut imag: usize, omag: usize, mut v: [u64; 6], mut msb: bool, ) -> [u64; 6] {
    while imag > omag {
        v = subtract_p::<VARTIME>(msb, &v, &MODS[(imag-1) / 2]);
        msb = false;
        imag = imag / 2;
    }
    return v
}

#[inline(always)]
pub const fn reduce_full_const<MagI, MagO, T: Timing>(mut v: [u64; 6], mut msb: bool) -> [u64; 6]
where MagI: RawMagnitude, MagO: RawMagnitude {
    let mut imag = MagI::MAG;
    while imag > MagO::MAG {
        v = subtract_pt::<T>(msb, &v, &MODS[(imag-1) / 2]);
        msb = false;
        imag = imag / 2;
    }
    return v
}

// The internal representation of this type is six 64-bit unsigned
// integers in little-endian order. `Fp` values are always in
// Montgomery form; i.e., Scalar(a) = aR mod p, with R = 2^384.
#[derive(Copy, Clone)]
pub struct Fp<const MAGNITUDE: usize = 0, const VARTIME: bool = false>(pub(crate) [u64; 6]);

// The internal representation of this type is six 64-bit unsigned
// integers in little-endian order. `Fp` values are always in
// Montgomery form; i.e., Scalar(a) = aR mod p, with R = 2^384.
#[derive(Copy, Clone)]
pub struct FpA<Mag: FpMagnitude = FpMag<0>, T: Timing = ConstTime>(pub(crate) [u64; 6], PhantomData<(Mag, T)>);

impl<const MAGNITUDE: usize, const VARTIME: bool> OtherMag for Fp<MAGNITUDE, VARTIME> {
    const MAGNITUDE: usize = MAGNITUDE;
    type Mag<const MAG2: usize> = Fp<MAG2, VARTIME>;
}

impl<const VARTIME: bool> Mag<1, [u64; 6]> for Fp<0, VARTIME> {
    type Prev = Never;
    type Next = Fp<1, VARTIME>;

    /// A multiple of the prime that is larger than this element could be (p).
    const MODULUS: [u64; 6] = MODULUS;

    #[inline(always)]
    fn make([v]: [[u64; 6]; 1]) -> Self {
        Self(v)
    }
    #[inline(always)]
    fn data(&self) -> [&[u64; 6]; 1] {
        [&self.0]
    }
    #[inline(always)]
    fn negate(&self) -> Self {
        self.neg()
    }
}

macro_rules! mag_impl {
    ($($($ua:literal),+ $(,)?)?) => {$($(
impl<const VARTIME: bool> Mag<1, [u64; 6]> for Fp<$ua, VARTIME> {
    type Prev = Fp<{$ua - 1}, VARTIME>;
    type Next = Fp<{$ua + 1}, VARTIME>;

    /// A multiple of the prime that is larger than this element could be (p).
    const MODULUS: [u64; 6] = add(&Self::Prev::MODULUS, &MODULUS);

    #[inline(always)]
    fn make([v]: [[u64; 6]; 1]) -> Self {
        Self(v)
    }
    #[inline(always)]
    fn data(&self) -> [&[u64; 6]; 1] {
        [&self.0]
    }
    #[inline(always)]
    fn negate(&self) -> Self {
        self.neg()
    }
}

impl<const VARTIME: bool> NonZero for Fp<$ua, VARTIME> {}
    )+)?};
}

mag_impl! {1, 2, 3, 4, 5, 6, 7}

impl<const VARTIME: bool> Mag<1, [u64; 6]> for Fp<8, VARTIME> {
    type Prev = Fp<7, VARTIME>;
    type Next = Never;

    /// A multiple of the prime that is larger than this element could be (p).
    const MODULUS: [u64; 6] = add(&Self::Prev::MODULUS, &MODULUS);

    #[inline(always)]
    fn make([v]: [[u64; 6]; 1]) -> Self {
        Self(v)
    }
    #[inline(always)]
    fn data(&self) -> [&[u64; 6]; 1] {
        [&self.0]
    }
    #[inline(always)]
    fn negate(&self) -> Self {
        Self::make([negate(self.data()[0], &Self::MODULUS)])
    }
}
impl<const VARTIME: bool> NonZero for Fp<8, VARTIME> {}

impl<const MAG2: usize, const VARTIME: bool> Ops<1, [u64; 6], Fp<MAG2, VARTIME>> for Fp<0, VARTIME>
where
    Fp<MAG2, VARTIME>: Mag<1, [u64; 6]>,
{
    type OpOut = <Fp<MAG2, VARTIME> as Mag<1, [u64; 6]>>::Next;
    #[inline(always)]
    fn add(lhs: &Self, rhs: &Fp<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([add(&lhs.0, &rhs.0)])
    }
    #[inline(always)]
    fn sub(lhs: &Self, rhs: &Fp<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([sub::<VARTIME>(&lhs.0, &rhs.0, <Self::OpOut>::MODULUS)])
    }
}


impl<const MAG1: usize, const MAG2: usize, const VARTIME: bool> Ops<1, [u64; 6], Fp<MAG2, VARTIME>> for Fp<MAG1, VARTIME>
where
    Fp<MAG1, VARTIME>: Mag<1, [u64; 6]> + NonZero,
    <Fp<MAG1, VARTIME> as Mag<1, [u64; 6]>>::Prev: Ops<1, [u64; 6], Fp<MAG2, VARTIME>>,
    Fp<MAG2, VARTIME>: Mag<1, [u64; 6]>,
{
    type OpOut =
        <<<Fp<MAG1, VARTIME> as Mag<1, [u64; 6]>>::Prev as Ops<1, [u64; 6], Fp<MAG2, VARTIME>>>::OpOut as Mag<1, [u64; 6]>>::Next;
    #[inline(always)]
    fn add(lhs: &Self, rhs: &Fp<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([add(lhs.data()[0], rhs.data()[0])])
    }
    #[inline(always)]
    fn sub(lhs: &Self, rhs: &Fp<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([sub::<VARTIME>(&lhs.0, &rhs.data()[0], <Self::OpOut>::MODULUS)])
    }
}

macro_rules! impl_double {
    ($pow:literal: $($($ua:literal),+ $(,)?)?) => {$($(
impl<const VARTIME: bool> DoubleOp<$pow> for Fp<$ua, VARTIME> {
    type DoubleOut = Fp<{($ua+1)*(1<<($pow+1))-1}, VARTIME>;
    fn double(lhs: &Self) -> Self::DoubleOut {
        Fp(double(&lhs.0, $pow+1))
    }
}
    )+)?};
}

impl_double!{0: 0, 1, 2, 3}
impl_double!{1: 0, 1}
impl_double!{2: 0}


impl<const MAGNITUDE: usize, const VARTIME: bool> MontOp for Fp<MAGNITUDE, VARTIME> {
    type MontOut = [u64; 6];
    fn montgomery_reduce(lhs: &Self) -> Self::MontOut {
        montgomery_reduce::<VARTIME>(MAGNITUDE, &lhs.0)
    }
}

impl<'a, 'b, const MAG1: usize, const MAG2: usize, const VARTIME: bool> Add<&'b Fp<MAG2, VARTIME>> for &'a Fp<MAG1, VARTIME>
where
    Fp<MAG1, VARTIME>: NonZero + Ops<1, [u64; 6], Fp<MAG2, VARTIME>>,
    <Fp<MAG1, VARTIME> as OtherMag>::Mag<MAG2>: Mag<1, [u64; 6]>,
    for<'j> &'j Fp<MAG2, VARTIME>: Into<&'j <Fp<MAG1, VARTIME> as OtherMag>::Mag<MAG2>>,
{
    type Output = <Fp<MAG1, VARTIME> as Ops<1, [u64; 6], Fp<MAG2, VARTIME>>>::OpOut;

    #[inline(always)]
    fn add(self, rhs: &'b Fp<MAG2, VARTIME>) -> Self::Output {
        Ops::add(self, rhs.into())
    }
}
impl<'a, 'b, const MAG1: usize, const MAG2: usize, const VARTIME: bool> Sub<&'b Fp<MAG2, VARTIME>> for &'a Fp<MAG1, VARTIME>
where
    Fp<MAG1, VARTIME>: NonZero + Ops<1, [u64; 6], Fp<MAG2, VARTIME>>,
    <Fp<MAG1, VARTIME> as OtherMag>::Mag<MAG2>: Mag<1, [u64; 6]>,
    for<'j> &'j Fp<MAG2, VARTIME>: Into<&'j <Fp<MAG1, VARTIME> as OtherMag>::Mag<MAG2>>,
{
    type Output = <Fp<MAG1, VARTIME> as Ops<1, [u64; 6], Fp<MAG2, VARTIME>>>::OpOut;

    #[inline(always)]
    fn sub(self, rhs: &'b Fp<MAG2, VARTIME>) -> Self::Output {
        Ops::sub(self, rhs.into())
    }
}
impl_binops_additive_output! {
{const MAG1: usize, const MAG2: usize, const VARTIME: bool}
{where Fp<MAG1, VARTIME>: NonZero+Ops<1, [u64; 6], Fp<MAG2, VARTIME>>, <Fp<MAG1, VARTIME> as OtherMag>::Mag<MAG2>: Mag<1, [u64; 6]>, for<'j> &'j Fp<MAG2, VARTIME>: Into<&'j <Fp<MAG1, VARTIME> as OtherMag>::Mag<MAG2>>}
{Fp<MAG1, VARTIME>}
{Fp<MAG2, VARTIME>}}

impl<const MAGNITUDE: usize, const VARTIME: bool> fmt::Debug for Fp<MAGNITUDE, VARTIME> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tmp = self.to_bytes();
        write!(f, "0x")?;
        for &b in tmp.iter() {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl<Mag: FpMagnitude, T: Timing> fmt::Debug for FpA<Mag, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let tmp = self.to_bytes();
        write!(f, "0x")?;
        for &b in tmp.iter() {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> Default for Fp<MAGNITUDE, VARTIME> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<Mag: FpMagnitude, T: Timing> Default for FpA<Mag, T> {
    fn default() -> Self {
        Self::zero()
    }
}

#[cfg(feature = "zeroize")]
impl<const MAGNITUDE: usize, const VARTIME: bool> zeroize::DefaultIsZeroes for Fp<MAGNITUDE, VARTIME> {}

#[cfg(feature = "zeroize")]
impl<Mag: FpMagnitude, T: Timing> zeroize::DefaultIsZeroes for FpA<Mag, T> {}

impl<const MAGNITUDE: usize, const VARTIME: bool> ConstantTimeEq for Fp<MAGNITUDE, VARTIME> {
    fn ct_eq(&self, other: &Self) -> Choice {
        ct_eq(&self.0, &other.0)
    }
}

impl<Mag: FpMagnitude, T: Timing> ConstantTimeEq for FpA<Mag, T> {
    fn ct_eq(&self, other: &Self) -> Choice {
        (*self).eq(other)
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> Eq for Fp<MAGNITUDE, VARTIME> {}
impl<const MAGNITUDE: usize, const VARTIME: bool> PartialEq for Fp<MAGNITUDE, VARTIME> {
    fn eq(&self, other: &Self) -> bool {
        match VARTIME {
            true => self.0 == other.0,
            false => bool::from(self.ct_eq(other)),
        }
    }
}

impl<Mag: FpMagnitude, T: Timing> Eq for FpA<Mag, T> {}
impl<Mag: FpMagnitude, T: Timing> PartialEq for FpA<Mag, T> {
    fn eq(&self, other: &Self) -> bool {
        match T::VAR {
            true => self.0 == other.0,
            false => bool::from(self.ct_eq(other)),
        }
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> ConditionallySelectable for Fp<MAGNITUDE, VARTIME> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fp([
            u64::conditional_select(&a.0[0], &b.0[0], choice),
            u64::conditional_select(&a.0[1], &b.0[1], choice),
            u64::conditional_select(&a.0[2], &b.0[2], choice),
            u64::conditional_select(&a.0[3], &b.0[3], choice),
            u64::conditional_select(&a.0[4], &b.0[4], choice),
            u64::conditional_select(&a.0[5], &b.0[5], choice),
        ])
    }
}

impl<Mag: FpMagnitude, T: Timing> ConditionallySelectable for FpA<Mag, T> {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        FpA([
            u64::conditional_select(&a.0[0], &b.0[0], choice),
            u64::conditional_select(&a.0[1], &b.0[1], choice),
            u64::conditional_select(&a.0[2], &b.0[2], choice),
            u64::conditional_select(&a.0[3], &b.0[3], choice),
            u64::conditional_select(&a.0[4], &b.0[4], choice),
            u64::conditional_select(&a.0[5], &b.0[5], choice),
        ], PhantomData)
    }
}

/// p = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
const MODULUS: [u64; 6] = [
    0xb9fe_ffff_ffff_aaab,
    0x1eab_fffe_b153_ffff,
    0x6730_d2a0_f6b0_f624,
    0x6477_4b84_f385_12bf,
    0x4b1b_a7b6_434b_acd7,
    0x1a01_11ea_397f_e69a,
];

macro_rules! mods {
    ($i:ident: $t:ty = $($m:literal)+) => {
const $i: [$t; {$(({let _ = $m; 1}) + )+ 0}] = [$(
    <Fp<$m, false> as Mag<1, _>>::MODULUS,
)+];
    };
}

mods!{MODS: [u64; 6] = 0 1 2 3 4 5 6 7 8}

const P2: [u64; 6] = double(&MODULUS, 1);
const P4: [u64; 6] = double(&P2, 1);
const P5: [u64; 6] = add(&P4, &MODULUS);
const P8: [u64; 6] = double(&P4, 1);

/// INV = -(p^{-1} mod 2^64) mod 2^64
const INV: u64 = 0x89f3_fffc_fffc_fffd;

/// R = 2^384 mod p
const R: Fp = Fp([
    0x7609_0000_0002_fffd,
    0xebf4_000b_c40c_0002,
    0x5f48_9857_53c7_58ba,
    0x77ce_5853_7052_5745,
    0x5c07_1a97_a256_ec6d,
    0x15f6_5ec3_fa80_e493,
]);

/// R2 = 2^(384*2) mod p
const R2: Fp = Fp([
    0xf4df_1f34_1c34_1746,
    0x0a76_e6a6_09d1_04f1,
    0x8de5_476c_4c95_b6d5,
    0x67eb_88a9_939d_83c0,
    0x9a79_3e85_b519_952d,
    0x1198_8fe5_92ca_e3aa,
]);

/// R3 = 2^(384*3) mod p
const R3: Fp = Fp([
    0xed48_ac6b_d94c_a1e0,
    0x315f_831e_03a7_adf8,
    0x9a53_352a_615e_29dd,
    0x34c0_4e5e_921e_1761,
    0x2512_d435_6572_4728,
    0x0aa6_3460_9175_5d4d,
]);

impl<'a, const MAGNITUDE: usize, const VARTIME: bool> Neg for &'a Fp<MAGNITUDE, VARTIME>
where Fp<MAGNITUDE, VARTIME>: Mag<1, [u64; 6]> {
    type Output = Fp<MAGNITUDE, VARTIME>;

    #[inline]
    fn neg(self) -> Fp<MAGNITUDE, VARTIME> {
        self.negate()
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> Neg for Fp<MAGNITUDE, VARTIME>
where Fp<MAGNITUDE, VARTIME>: Mag<1, [u64; 6]> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        -&self
    }
}

impl<'a, 'b, const VARTIME: bool> Sub<&'b Fp<0, VARTIME>> for &'a Fp<0, VARTIME> {
    type Output = Fp<0, VARTIME>;

    #[inline]
    fn sub(self, rhs: &'b Fp<0, VARTIME>) -> Fp<0, VARTIME> {
        self.sub(rhs)
    }
}

impl<'a, 'b, const VARTIME: bool> Add<&'b Fp<0, VARTIME>> for &'a Fp<0, VARTIME> {
    type Output = Fp<0, VARTIME>;

    #[inline]
    fn add(self, rhs: &'b Fp<0, VARTIME>) -> Fp<0, VARTIME> {
        self.add(rhs)
    }
}

impl<'a, 'b, const VARTIME: bool> Mul<&'b Fp<0, VARTIME>> for &'a Fp<0, VARTIME> {
    type Output = Fp<0, VARTIME>;

    #[inline]
    fn mul(self, rhs: &'b Fp<0, VARTIME>) -> Fp<0, VARTIME> {
        self.mul(rhs)
    }
}

impl_binops_additive!{
    {const VARTIME: bool}
    {}
    {Fp<0, VARTIME>}
    {Fp<0, VARTIME>}
}
impl_binops_multiplicative!{
    {const VARTIME: bool}
    {}
    {Fp<0, VARTIME>}
    {Fp<0, VARTIME>}
}

pub type FpDouble<Mag> = MagFp<MagDouble<Mag>>;
pub type FpLsh<Mag, const P: usize> = MagFp<MagLsh<Mag, P>>;
pub type FpAdd<Lhs, Rhs> = MagFp<MagAdd<Lhs, Rhs>>;
pub type FpSub<Lhs, Rhs> = MagFp<MagSub<Lhs, Rhs>>;
pub type FpSquare<Mag> = MagFpWide<MagSquare<Mag>>;
pub type FpMul<Lhs, Rhs> = MagFpWide<MagMul<Lhs, Rhs>>;
pub type FpPow<Mag> = MagFp<MagReduce<FpSquare<Mag>>>;
pub type FpInvert<Mag> = FpPow<Mag>;
pub type FpSqrt<Mag> = FpPow<Mag>;

impl<Mag: FpMagnitude, T: Timing> FpA<Mag, T> {
    /// Constructs an element of `Fp` without checking that it is
    /// canonical.
    #[inline]
    pub const fn from_raw_unchecked(v: [u64; 6]) -> Self {
        Self(v, PhantomData)
    }

    /// Returns zero, the additive identity.
    #[inline]
    pub const fn zero() -> Self {
        Self::from_raw_unchecked([0; 6])
    }

    /// Returns one, the multiplicative identity.
    #[inline]
    pub const fn one() -> Self {
        Self::from_raw_unchecked(R.0)
    }

    pub fn random(mut rng: impl RngCore) -> Self {
        let mut bytes = [0u8; 96];
        rng.fill_bytes(&mut bytes);

        // Parse the random bytes as a big-endian number, to match Fp encoding order.
        Self::from_u768([
            be_bytes_to_u64!(bytes[0..]),
            be_bytes_to_u64!(bytes[8..]),
            be_bytes_to_u64!(bytes[16..]),
            be_bytes_to_u64!(bytes[24..]),
            be_bytes_to_u64!(bytes[32..]),
            be_bytes_to_u64!(bytes[40..]),
            be_bytes_to_u64!(bytes[48..]),
            be_bytes_to_u64!(bytes[56..]),
            be_bytes_to_u64!(bytes[64..]),
            be_bytes_to_u64!(bytes[72..]),
            be_bytes_to_u64!(bytes[80..]),
            be_bytes_to_u64!(bytes[88..]),
        ])
    }

    /// Reduces a big-endian 64-bit limb representation of a 768-bit number.
    fn from_u768(limbs: [u64; 12]) -> Self {
        // We reduce an arbitrary 768-bit number by decomposing it into two 384-bit digits
        // with the higher bits multiplied by 2^384. Thus, we perform two reductions
        //
        // 1. the lower bits are multiplied by R^2, as normal
        // 2. the upper bits are multiplied by R^2 * 2^384 = R^3
        //
        // and computing their sum in the field. It remains to see that arbitrary 384-bit
        // numbers can be placed into Montgomery form safely using the reduction. The
        // reduction works so long as the product is less than R=2^384 multiplied by
        // the modulus. This holds because for any `c` smaller than the modulus, we have
        // that (2^384 - 1)*c is an acceptable product for the reduction. Therefore, the
        // reduction always works so long as `c` is in the field; in this case it is either the
        // constant `R2` or `R3`.
        
        let d0 = wide::mul_wide(&[limbs[5], limbs[4], limbs[3], limbs[2], limbs[1], limbs[0]], &R2.0);
        let d1 = wide::mul_wide(&[limbs[11], limbs[10], limbs[9], limbs[8], limbs[7], limbs[6]], &R3.0);

        // Convert to Montgomery form
        let (v, _msb) = wide::montgomery_reduce_wide(&wide::add_wide(&d0, &d1));

        if cfg!(debug_assertions) && _msb {
            panic!("carry != 0");
        }
        // $Solve[b=((R-1)*((R^2 mod p)+(R^3 mod p)+p))/(R*p) && m==1 && R==2^384 && p==4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787,b]$
        // magnitude ~= 2.08
        //let v = reduce_full::<VARTIME>(3, Mag::MAG, v, false);
        let v = reduce_full_const::<FpMag<3>, Mag, T>(v, false);

        Self::from_raw_unchecked(v)
    }

    /// Returns one, the multiplicative identity.
    #[inline]
    pub const fn vartime<T2: Timing>(self) -> FpA<Mag, T2> {
        FpA::from_raw_unchecked(self.0)
    }

    /// Reduce the magnitude of an `Fp`
    #[inline]
    pub const fn mag<MagR: FpMagnitude>(self) -> FpA<MagR, T> {
        // let v = reduce_full::<VARTIME>(Mag::MAG, MagR::MAG, self.0, false)
        let v = reduce_full_const::<Mag, MagR, T>(self.0, false);
        FpA::from_raw_unchecked(v)
    }

    #[inline]
    pub fn eq<RMag: FpMagnitude>(self, rhs: &FpA<RMag, T>) -> Choice {
        self.sub(rhs).is_zero()
    }

    #[inline]
    pub const fn eq_vartime<RMag: FpMagnitude>(self, rhs: &FpA<RMag, T>) -> bool {
        self.sub(rhs).is_zero_vartime()
    }

    #[inline]
    pub fn is_zero(&self) -> Choice {
        let v = reduce_full_const::<Mag, FpMag<0>, T>(self.0, false);
        ct_eq(&v, &Self::zero().0)
    }

    #[inline]
    pub const fn is_zero_vartime(&self) -> bool {
        let v = reduce_full_const::<Mag, FpMag<0>, T>(self.0, false);
        eq_vartime(&v, &Self::zero().0)
    }

    /// Constructs an element of `Fp` ensuring that it is canonical.
    pub const fn from_raw(v: [u64; 6]) -> Self {
        // let v = reduce_full::<VARTIME>(11, Mag::MAG, v, false);
        let v = reduce_full_const::<FpMag<11>, Mag, T>(v, false);
        Self::from_raw_unchecked(v)
    }

    #[inline(always)]
    pub(crate) const fn montgomery_reduce(&self) -> [u64; 6] {
        montgomery_reducet::<T>(Mag::MAG, &self.0)
    }

    /// Converts an element of `Fp` into a byte representation in
    /// big-endian byte order.
    pub const fn to_bytes(self) -> [u8; 48] {
        // Turn into canonical form by computing
        // (a.R) / R = a
        let tmp = self.montgomery_reduce();

        let res = copy_bytes([0; 48], 0, tmp[5].to_be_bytes());
        let res = copy_bytes(res, 8, tmp[4].to_be_bytes());
        let res = copy_bytes(res, 16, tmp[3].to_be_bytes());
        let res = copy_bytes(res, 24, tmp[2].to_be_bytes());
        let res = copy_bytes(res, 32, tmp[1].to_be_bytes());
        let res = copy_bytes(res, 40, tmp[0].to_be_bytes());

        res
    }

    #[inline]
    pub const fn neg(&self) -> Self {
        Self::from_raw_unchecked(match T::VAR {
            true if self.is_zero_vartime() => self.0,
            true => negate(&self.0, &MODS[Mag::MAG]),
            false => {
                // Let's use a mask if `self` was zero, which would mean
                // the result of the subtraction is p.
                let mask = (((self.0[0] | self.0[1] | self.0[2] | self.0[3] | self.0[4] | self.0[5]) == 0)
                as u64)
                .wrapping_sub(1);

                let v = negate(&self.0, &MODS[Mag::MAG]);
                [
                    v[0] & mask,
                    v[1] & mask,
                    v[2] & mask,
                    v[3] & mask,
                    v[4] & mask,
                    v[5] & mask,
                ]
            }
        })
    }

    #[inline]
    pub const fn double(&self) -> FpA<FpDouble<Mag>, T> {
        let (v, msb) = double_c(&self.0, 1);
        // let v = reduce_full::<T>(MagDouble::<Mag>::MAG, FpDouble::<Mag>::MAG, v, msb);
        let v = reduce_full_const::<MagDouble<Mag>, FpDouble<Mag>, T>(v, msb);
        FpA::from_raw_unchecked(v)
        
    }

    #[inline]
    pub const fn lsh<const P: usize>(&self) -> FpA<FpLsh<Mag, P>, T>
    where FpMag<P>: RawMagnitude {
        let (v, msb) = double_c(&self.0, P as u32);
        // let v = reduce_full::<T>(MagLsh::<Mag, P>::MAG, FpLsh::<Mag, P>::MAG, v, msb);
        let v = reduce_full_const::<MagLsh<Mag, P>, FpLsh<Mag, P>, T>(v, msb);
        FpA::from_raw_unchecked(v)
    }

    #[inline]
    pub const fn add<RMag: FpMagnitude>(&self, rhs: &FpA<RMag, T>) -> FpA<FpAdd<Mag, RMag>, T> {
        let (v, msb) = add_c(&self.0, &rhs.0);
        // let v = reduce_full::<T>(MagAdd::<Mag, RMag>::MAG, FpAdd::<Mag, RMag>::MAG, v, msb);
        let v = reduce_full_const::<MagAdd<Mag, RMag>, FpAdd<Mag, RMag>, T>(v, msb);
        FpA::from_raw_unchecked(v)
    }

    #[inline]
    pub const fn sub<RMag: FpMagnitude>(&self, rhs: &FpA<RMag, T>) -> FpA<FpSub<Mag, RMag>, T> {
        let v = subt::<T>(&self.0, &rhs.0, MODS[FpSub::<Mag, RMag>::MAG]);
        FpA::from_raw_unchecked(v)
    }

    /// Squares this element.
    #[inline]
    pub const fn square(&self) -> FpAWide<FpSquare<Mag>, T> {
        FpAWide::from_raw_unchecked(square_wide(&self.0))
    }

    /// Multiply this element by another.
    #[inline]
    pub const fn mul<RMag: FpMagnitude>(&self, rhs: &FpA<RMag, T>) -> FpAWide<FpMul<Mag, RMag>, T> {
        FpAWide::from_raw_unchecked(mul_wide(&self.0, &rhs.0))
    }

    /// Although this is labeled "vartime", it is only
    /// variable time with respect to the exponent. It
    /// is also not exposed in the public API.
    pub const fn pow_vartime(&self, by: &[u64; 6]) -> FpA<FpPow<Mag>, T> {
        let mut res = FpA::one();
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

    /// Exponentiate by p - 2
    #[inline]
    const fn try_invert(&self) -> FpA<FpInvert<Mag>, T> {
        self.pow_vartime(&[
            0xb9fe_ffff_ffff_aaa9,
            0x1eab_fffe_b153_ffff,
            0x6730_d2a0_f6b0_f624,
            0x6477_4b84_f385_12bf,
            0x4b1b_a7b6_434b_acd7,
            0x1a01_11ea_397f_e69a,
        ])
    }

    /// Computes the multiplicative inverse of this field
    /// element, returning None in the case that this element
    /// is zero.
    #[inline]
    pub fn invert(&self) -> CtOption<FpA<FpInvert<Mag>, T>> {
        let t = self.try_invert();
        CtOption::new(t, !self.is_zero())
    }

    /// Computes the multiplicative inverse of this field
    /// element, returning None in the case that this element
    /// is zero.
    #[inline]
    pub const fn invert_vartime(&self) -> Option<FpA<FpInvert<Mag>, T>> {
        if self.is_zero_vartime() {
            None
        } else {
            Some(self.try_invert())
        }
    }

    // We use Shank's method, as p = 3 (mod 4). This means
    // we only need to exponentiate by (p+1)/4. This only
    // works for elements that are actually quadratic residue,
    // so we check that we got the correct result at the end.
    #[inline]
    const fn try_sqrt(&self) -> FpA<FpSqrt<Mag>, T> {
        self.pow_vartime(&[
            0xee7f_bfff_ffff_eaab,
            0x07aa_ffff_ac54_ffff,
            0xd9cc_34a8_3dac_3d89,
            0xd91d_d2e1_3ce1_44af,
            0x92c6_e9ed_90d2_eb35,
            0x0680_447a_8e5f_f9a6,
        ])
    }

    #[inline]
    pub fn sqrt(&self) -> CtOption<FpA<FpSqrt<Mag>, T>> {
        let sqrt = self.try_sqrt();
        let v = sqrt.square().montgomery_reduce().sub(&self);
        CtOption::new(sqrt, v.is_zero())
    }

    #[inline]
    pub const fn sqrt_vartime(&self) -> Option<FpA<FpSqrt<Mag>, T>> {
        let sqrt = self.try_sqrt();
        let v = sqrt.square().montgomery_reduce().sub(&self);
        if v.is_zero_vartime() {
            Some(sqrt)
        } else {
            None
        }
    }
}

impl<T: Timing> FpA<FpMag<0>, T> {
    /// Attempts to convert a big-endian byte representation of
    /// a scalar into an `Fp`, failing if the input is not canonical.
    pub fn from_bytes(bytes: &[u8; 48]) -> CtOption<Self> {
        let mut tmp = [0; 6];

        tmp[5] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[0..8]).unwrap());
        tmp[4] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[8..16]).unwrap());
        tmp[3] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[16..24]).unwrap());
        tmp[2] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[24..32]).unwrap());
        tmp[1] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[32..40]).unwrap());
        tmp[0] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[40..48]).unwrap());

        // Try to subtract the modulus
        let (_, borrow) = borrowing_sub(tmp[0], MODULUS[0], false);
        let (_, borrow) = borrowing_sub(tmp[1], MODULUS[1], borrow);
        let (_, borrow) = borrowing_sub(tmp[2], MODULUS[2], borrow);
        let (_, borrow) = borrowing_sub(tmp[3], MODULUS[3], borrow);
        let (_, borrow) = borrowing_sub(tmp[4], MODULUS[4], borrow);
        let (_, borrow) = borrowing_sub(tmp[5], MODULUS[5], borrow);

        // If the element is smaller than MODULUS then the
        // subtraction will underflow, producing a borrow value
        // of 0xffff...ffff. Otherwise, it'll be zero.
        let is_some = (borrow as u8) & 1;

        // Convert to Montgomery form by computing
        // (a.R^0 * R^2) / R = a.R
        let tmp = Self::from_raw_unchecked(tmp).mul(&Self::from_raw_unchecked(R2.0)).montgomery_reduce().mag();

        CtOption::new(tmp, Choice::from(is_some))
    }

    /// Returns whether or not this element is strictly lexicographically
    /// larger than its negation.
    pub const fn lexicographically_largest_vartime(&self) -> bool {
        // This can be determined by checking to see if the element is
        // larger than (p - 1) // 2. If we subtract by ((p - 1) // 2) + 1
        // and there is no underflow, then the element must be larger than
        // (p - 1) // 2.

        // First, because self is in Montgomery form we need to reduce it
        let tmp = self.montgomery_reduce();

        let (_, borrow) = borrowing_sub(tmp[0], 0xdcff_7fff_ffff_d556, false);
        let (_, borrow) = borrowing_sub(tmp[1], 0x0f55_ffff_58a9_ffff, borrow);
        let (_, borrow) = borrowing_sub(tmp[2], 0xb398_6950_7b58_7b12, borrow);
        let (_, borrow) = borrowing_sub(tmp[3], 0xb23b_a5c2_79c2_895f, borrow);
        let (_, borrow) = borrowing_sub(tmp[4], 0x258d_d3db_21a5_d66b, borrow);
        let (_, borrow) = borrowing_sub(tmp[5], 0x0d00_88f5_1cbf_f34d, borrow);

        // If the element was smaller, the subtraction will underflow
        // producing a borrow value of 0xffff...ffff, otherwise it will
        // be zero. We create a Choice representing true if there was
        // overflow (and so this element is not lexicographically larger
        // than its negation) and then negate it.
        !borrow
    }

    /// Returns whether or not this element is strictly lexicographically
    /// larger than its negation.
    pub fn lexicographically_largest(&self) -> Choice {
        Choice::from(self.lexicographically_largest_vartime() as u8)
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> Fp<MAGNITUDE, VARTIME> {
    /// Returns zero, the additive identity.
    #[inline]
    pub const fn zero() -> Self {
        Self([0, 0, 0, 0, 0, 0])
    }

    /// Returns one, the multiplicative identity.
    #[inline]
    pub const fn one() -> Self {
        Self(R.0)
    }

    /// Returns one, the multiplicative identity.
    #[inline]
    pub const fn vartime<const VARTIME2: bool>(self) -> Fp<MAGNITUDE, VARTIME2> {
        Fp(self.0)
    }

    #[inline]
    pub const fn eq_vartime(&self, rhs: &Self) -> bool {
        eq_vartime(&self.0, &rhs.0)
    }

    #[inline]
    pub fn is_zero(&self) -> Choice {
        let mut c = self.ct_eq(&Fp::zero());
        let mut i = MAGNITUDE;
        while i > 0 {
            c |= ct_eq(&self.0, &MODS[i]);
            i -= 1;
        }
        c
    }

    #[inline]
    pub const fn is_zero_vartime(&self) -> bool {
        let mut i = MAGNITUDE;
        while i > 0 {
            if eq_vartime(&self.0, &MODS[i]) {
                return true
            }
            i -= 1;
        }
        self.eq_vartime(&Fp::zero())
    }

    /// Constructs an element of `Fp` without checking that it is
    /// canonical.
    #[inline]
    pub const fn from_raw_unchecked(v: [u64; 6]) -> Self {
        Self(v)
    }

    /// Constructs an element of `Fp` ensuring that it is canonical.
    pub const fn from_raw(mut v: [u64; 6]) -> Self {
        // Attempt to subtract all possible multiples of the modulus, to ensure
        // the value is smaller than the modulus.
        match MAGNITUDE {
            0 => {
                v = subtract_p::<VARTIME>(false, &v, &MODS[5]);
                v = subtract_p::<VARTIME>(false, &v, &MODS[2]);
                v = subtract_p::<VARTIME>(false, &v, &MODS[1]);
                v = subtract_p::<VARTIME>(false, &v, &MODS[0]);
            },
            1 => {
                v = subtract_p::<VARTIME>(false, &v, &MODS[5]);
                v = subtract_p::<VARTIME>(false, &v, &MODS[2]);
                v = subtract_p::<VARTIME>(false, &v, &MODS[1]);
            },
            2 => {
                v = subtract_p::<VARTIME>(false, &v, &MODS[5]);
                v = subtract_p::<VARTIME>(false, &v, &MODS[2]);
            },
            3 => {
                v = subtract_p::<VARTIME>(false, &v, &MODS[5]);
                v = subtract_p::<VARTIME>(false, &v, &MODS[3]);
            },
            4 => {
                v = subtract_p::<VARTIME>(false, &v, &MODS[5]);
                v = subtract_p::<VARTIME>(false, &v, &MODS[4]);
            },
            mag => {
                v = subtract_p::<VARTIME>(false, &v, &MODS[mag]);
            },
        }
        Self(v)
    }

    #[inline(always)]
    pub(crate) const fn montgomery_reduce(&self) -> [u64; 6] {
        montgomery_reduce::<VARTIME>(MAGNITUDE, &self.0)
    }

    /// Converts an element of `Fp` into a byte representation in
    /// big-endian byte order.
    pub const fn to_bytes(self) -> [u8; 48] {
        // Turn into canonical form by computing
        // (a.R) / R = a
        let tmp = self.montgomery_reduce();

        let res = copy_bytes([0; 48], 0, tmp[5].to_be_bytes());
        let res = copy_bytes(res, 8, tmp[4].to_be_bytes());
        let res = copy_bytes(res, 16, tmp[3].to_be_bytes());
        let res = copy_bytes(res, 24, tmp[2].to_be_bytes());
        let res = copy_bytes(res, 32, tmp[1].to_be_bytes());
        let res = copy_bytes(res, 40, tmp[0].to_be_bytes());

        res
    }

    /// Reduce the magnitude of an `Fp` to `0`
    pub const fn reduce_full(self) -> Fp<0, VARTIME> {
        let mut v = self.0;
        if MAGNITUDE >= 8 {
            v = subtract_p::<VARTIME>(false, &v, &P8)
        }
        if MAGNITUDE >= 4 {
            v = subtract_p::<VARTIME>(false, &v, &P4)
        }
        if MAGNITUDE >= 2 {
            v = subtract_p::<VARTIME>(false, &v, &P2)
        }
        if MAGNITUDE >= 1 {
            v = subtract_p::<VARTIME>(false, &v, &MODULUS)
        }
        Fp(v)
    }

    #[inline]
    pub const fn neg(&self) -> Self {
        match VARTIME {
            true if self.is_zero_vartime() => *self,
            true => Self(negate(&self.0, &MODS[MAGNITUDE])),
            false => {
                // Let's use a mask if `self` was zero, which would mean
                // the result of the subtraction is p.
                let mask = (((self.0[0] | self.0[1] | self.0[2] | self.0[3] | self.0[4] | self.0[5]) == 0)
                as u64)
                .wrapping_sub(1);

                let v = negate(&self.0, &MODS[MAGNITUDE]);
                Self([
                    v[0] & mask,
                    v[1] & mask,
                    v[2] & mask,
                    v[3] & mask,
                    v[4] & mask,
                    v[5] & mask,
                ])
            }
        }
    }

    /// Squares this element.
    #[inline]
    pub const fn square(&self) -> Self {
        let mut v = montgomery_reduce_wide(&square_wide(&self.0)).0;
        
        // $Solve[b=((m*p)^2 + R*p − p) / (R*p) && m == 1 && R==2^384 && p==4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787, b]$
        // We can see that `montgomery_reduce_wide` will produce results with an upper bound of $p + 0.1015788266026898895 * m^2*p$
        // This means we actually only have to reduce the item in two cases
        match MAGNITUDE {
            0 => v = subtract_p::<VARTIME>(false, &v, &<Fp<0, false> as Mag<1, _>>::MODULUS),
            8 => v = subtract_p::<VARTIME>(false, &v, &<Fp<8, false> as Mag<1, _>>::MODULUS),
            _ => {},
        }
        Self(v)
    }

    /// Multiply this element by another.
    #[inline]
    pub const fn mul(&self, rhs: &Fp<MAGNITUDE, VARTIME>) -> Self {
        let mut v = montgomery_reduce_wide(&mul_wide(&self.0, &rhs.0)).0;
        
        // $Solve[b=((m*p)^2 + R*p − p) / (R*p) && m == 1 && R==2^384 && p==4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787, b]$
        // We can see that `montgomery_reduce_wide` will produce results with an upper bound of $p + 0.1015788266026898895 * m^2*p$
        // This means we actually only have to reduce the item in two cases
        match MAGNITUDE {
            0 => v = subtract_p::<VARTIME>(false, &v, &<Fp<0, false> as Mag<1, _>>::MODULUS),
            8 => v = subtract_p::<VARTIME>(false, &v, &<Fp<8, false> as Mag<1, _>>::MODULUS),
            _ => {},
        }
        Self(v)
    }

    #[inline]
    pub const fn add(&self, rhs: &Self) -> Self {
        // Attempt to subtract the modulus, to ensure the value
        // is smaller than the modulus.
        Fp(subtract_p::<VARTIME>(false, &add(&self.0, &rhs.0), &MODS[MAGNITUDE]))
    }

    #[inline]
    pub const fn add2<const RMAG: usize, const SMAG: usize>(&self, rhs: &Fp<RMAG, VARTIME>) -> Fp<SMAG, VARTIME>
    where Self: Ops<1, [u64; 6], Fp<RMAG, VARTIME>, OpOut = Fp<SMAG, VARTIME>> {
        Fp(add(&self.0, &rhs.0))
    }

    #[inline]
    pub const fn double(&self) -> Self {
        // Attempt to subtract the modulus, to ensure the value
        // is smaller than the modulus.
        Fp(subtract_p::<VARTIME>(false, &double(&self.0, 1), &MODS[MAGNITUDE]))
    }

    #[inline]
    pub const fn sub(&self, rhs: &Self) -> Self {
        Fp(sub::<VARTIME>(&self.0, &rhs.0, MODS[MAGNITUDE]))
    }

    /// Although this is labeled "vartime", it is only
    /// variable time with respect to the exponent. It
    /// is also not exposed in the public API.
    pub const fn pow_vartime(&self, by: &[u64; 6]) -> Self {
        if MAGNITUDE == 0 {
            return Fp(Fp::<1>(self.0).pow_vartime(by).reduce_full().0);
        }
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

    #[inline]
    /// Returns `c = a.fold(0, |acc, (a_i)| acc + a_i * a_i)`.
    pub(crate) const fn sum_of_squares<const T: usize>(a: [Self; T]) -> Self {
        if a.is_empty() {
            return Self::zero()
        }
        let mut s = square_wide(&a[0].0);
        let mut i = 1;

        let mut mag = (MAGNITUDE+1)*(MAGNITUDE+1);
        while i < a.len() {
            let msb;
            (s, msb) = add_wide_c(&s, &square_wide(&a[i].0));
            mag += (MAGNITUDE+1)*(MAGNITUDE+1);
            if mag > 96 {
                s = subtract_p_wide::<VARTIME>(msb, &s, &WIDE_MODS[mag/2 - 1]);
                mag = (mag - 1) / 2;
            }
            i += 1;
        }

        Self(montgomery_reduce_full::<VARTIME>(mag, MAGNITUDE, &s))
    }

    /// Returns `c = a.zip(b).fold(0, |acc, (a_i, b_i)| acc + a_i * b_i)`.
    ///
    /// Implements Algorithm 2 from Patrick Longa's
    /// [ePrint 2022-367](https://eprint.iacr.org/2022/367) §3.
    #[inline]
    pub(crate) const fn sum_of_products<const T: usize>(a: [Self; T], b: [Self; T]) -> Self {
        // For a single `a x b` multiplication, operand scanning (schoolbook) takes each
        // limb of `a` in turn, and multiplies it by all of the limbs of `b` to compute
        // the result as a double-width intermediate representation, which is then fully
        // reduced at the end. Here however we have pairs of multiplications (a_i, b_i),
        // the results of which are summed.
        //
        // The intuition for this algorithm is two-fold:
        // - We can interleave the operand scanning for each pair, by processing the jth
        //   limb of each `a_i` together. As these have the same offset within the overall
        //   operand scanning flow, their results can be summed directly.
        // - We can interleave the multiplication and reduction steps, resulting in a
        //   single bitshift by the limb size after each iteration. This means we only
        //   need to store a single extra limb overall, instead of keeping around all the
        //   intermediate results and eventually having twice as many limbs.

        // Algorithm 2, line 2
        let (mut u0, mut u1, mut u2, mut u3, mut u4, mut u5) = (0, 0, 0, 0, 0, 0);
        let mut j = 0;
        while j < 6 {
            let (mut t0, mut t1, mut t2, mut t3, mut t4, mut t5, mut t6) = (u0, u1, u2, u3, u4, u5, 0);
            let mut i = 0;
            // For each pair in the overall sum of products:
            while i < T {
                // Compute digit_j x row and accumulate into `u`.
                let mut carry;
                (t0, carry) = mac(t0, a[i].0[j], b[i].0[0], 0);
                (t1, carry) = mac(t1, a[i].0[j], b[i].0[1], carry);
                (t2, carry) = mac(t2, a[i].0[j], b[i].0[2], carry);
                (t3, carry) = mac(t3, a[i].0[j], b[i].0[3], carry);
                (t4, carry) = mac(t4, a[i].0[j], b[i].0[4], carry);
                (t5, carry) = mac(t5, a[i].0[j], b[i].0[5], carry);
                (t6, _) = adc(t6, 0, carry);

                i += 1;
            }

            // Algorithm 2, lines 4-5
            // This is a single step of the usual Montgomery reduction process.
            let k = t0.wrapping_mul(INV);
            let (_, carry) = mac(t0, k, MODULUS[0], 0);
            let (r1, carry) = mac(t1, k, MODULUS[1], carry);
            let (r2, carry) = mac(t2, k, MODULUS[2], carry);
            let (r3, carry) = mac(t3, k, MODULUS[3], carry);
            let (r4, carry) = mac(t4, k, MODULUS[4], carry);
            let (r5, carry) = mac(t5, k, MODULUS[5], carry);
            let (r6, _) = adc(t6, 0, carry);

            (u0, u1, u2, u3, u4, u5) = (r1, r2, r3, r4, r5, r6);
            j += 1;
        }

        // let (u0, u1, u2, u3, u4, u5) =
        //     (0..6).fold((0, 0, 0, 0, 0, 0), |(u0, u1, u2, u3, u4, u5), j| {
        //         // Algorithm 2, line 3
        //         // For each pair in the overall sum of products:
        //         let (t0, t1, t2, t3, t4, t5, t6) = (0..T).fold(
        //             (u0, u1, u2, u3, u4, u5, 0),
        //             |(t0, t1, t2, t3, t4, t5, t6), i| {
        //                 // Compute digit_j x row and accumulate into `u`.
        //                 let (t0, carry) = mac(t0, a[i].0[j], b[i].0[0], 0);
        //                 let (t1, carry) = mac(t1, a[i].0[j], b[i].0[1], carry);
        //                 let (t2, carry) = mac(t2, a[i].0[j], b[i].0[2], carry);
        //                 let (t3, carry) = mac(t3, a[i].0[j], b[i].0[3], carry);
        //                 let (t4, carry) = mac(t4, a[i].0[j], b[i].0[4], carry);
        //                 let (t5, carry) = mac(t5, a[i].0[j], b[i].0[5], carry);
        //                 let (t6, _) = adc(t6, 0, carry);

        //                 (t0, t1, t2, t3, t4, t5, t6)
        //             },
        //         );

        //         // Algorithm 2, lines 4-5
        //         // This is a single step of the usual Montgomery reduction process.
        //         let k = t0.wrapping_mul(INV);
        //         let (_, carry) = mac(t0, k, MODULUS[0], 0);
        //         let (r1, carry) = mac(t1, k, MODULUS[1], carry);
        //         let (r2, carry) = mac(t2, k, MODULUS[2], carry);
        //         let (r3, carry) = mac(t3, k, MODULUS[3], carry);
        //         let (r4, carry) = mac(t4, k, MODULUS[4], carry);
        //         let (r5, carry) = mac(t5, k, MODULUS[5], carry);
        //         let (r6, _) = adc(t6, 0, carry);

        //         (r1, r2, r3, r4, r5, r6)
        //     });

        // Because we represent F_p elements in non-redundant form, we need a final
        // conditional subtraction to ensure the output is in range.
        Fp(subtract_p::<VARTIME>(false, &[u0, u1, u2, u3, u4, u5], &MODS[MAGNITUDE]))
    }

    /// Exponentiate by p - 2
    #[inline]
    const fn try_invert(&self) -> Self {
        self.pow_vartime(&[
            0xb9fe_ffff_ffff_aaa9,
            0x1eab_fffe_b153_ffff,
            0x6730_d2a0_f6b0_f624,
            0x6477_4b84_f385_12bf,
            0x4b1b_a7b6_434b_acd7,
            0x1a01_11ea_397f_e69a,
        ])
    }

    /// Computes the multiplicative inverse of this field
    /// element, returning None in the case that this element
    /// is zero.
    #[inline]
    pub fn invert(&self) -> CtOption<Self> {
        let t = self.try_invert();
        CtOption::new(t, !self.is_zero())
    }

    /// Computes the multiplicative inverse of this field
    /// element, returning None in the case that this element
    /// is zero.
    #[inline]
    pub const fn invert_vartime(&self) -> Option<Self> {
        if self.is_zero_vartime() {
            None
        } else {
            Some(self.try_invert())
        }
    }

    // We use Shank's method, as p = 3 (mod 4). This means
    // we only need to exponentiate by (p+1)/4. This only
    // works for elements that are actually quadratic residue,
    // so we check that we got the correct result at the end.
    #[inline]
    const fn try_sqrt(&self) -> Self {
        self.pow_vartime(&[
            0xee7f_bfff_ffff_eaab,
            0x07aa_ffff_ac54_ffff,
            0xd9cc_34a8_3dac_3d89,
            0xd91d_d2e1_3ce1_44af,
            0x92c6_e9ed_90d2_eb35,
            0x0680_447a_8e5f_f9a6,
        ])
    }

    #[inline]
    pub fn sqrt(&self) -> CtOption<Self> {
        let sqrt = self.try_sqrt();
        CtOption::new(sqrt, sqrt.square().ct_eq(self))
    }

    #[inline]
    pub const fn sqrt_vartime(&self) -> Option<Self> {
        let sqrt = self.try_sqrt();
        if sqrt.square().eq_vartime(self) {
            Some(sqrt)
        } else {
            None
        }
    }
}

impl<const VARTIME: bool> Fp<0, VARTIME> {
    /// Attempts to convert a big-endian byte representation of
    /// a scalar into an `Fp`, failing if the input is not canonical.
    pub fn from_bytes(bytes: &[u8; 48]) -> CtOption<Self> {
        let mut tmp = Self([0, 0, 0, 0, 0, 0]);

        tmp.0[5] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[0..8]).unwrap());
        tmp.0[4] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[8..16]).unwrap());
        tmp.0[3] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[16..24]).unwrap());
        tmp.0[2] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[24..32]).unwrap());
        tmp.0[1] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[32..40]).unwrap());
        tmp.0[0] = u64::from_be_bytes(<[u8; 8]>::try_from(&bytes[40..48]).unwrap());

        // Try to subtract the modulus
        let (_, borrow) = borrowing_sub(tmp.0[0], MODULUS[0], false);
        let (_, borrow) = borrowing_sub(tmp.0[1], MODULUS[1], borrow);
        let (_, borrow) = borrowing_sub(tmp.0[2], MODULUS[2], borrow);
        let (_, borrow) = borrowing_sub(tmp.0[3], MODULUS[3], borrow);
        let (_, borrow) = borrowing_sub(tmp.0[4], MODULUS[4], borrow);
        let (_, borrow) = borrowing_sub(tmp.0[5], MODULUS[5], borrow);

        // If the element is smaller than MODULUS then the
        // subtraction will underflow, producing a borrow value
        // of 0xffff...ffff. Otherwise, it'll be zero.
        let is_some = (borrow as u8) & 1;

        // Convert to Montgomery form by computing
        // (a.R^0 * R^2) / R = a.R
        tmp = tmp.mul(&Fp(R2.0));

        CtOption::new(tmp, Choice::from(is_some))
    }

    pub fn random(mut rng: impl RngCore) -> Self {
        let mut bytes = [0u8; 96];
        rng.fill_bytes(&mut bytes);

        // Parse the random bytes as a big-endian number, to match Fp encoding order.
        Self::from_u768([
            be_bytes_to_u64!(bytes[0..]),
            be_bytes_to_u64!(bytes[8..]),
            be_bytes_to_u64!(bytes[16..]),
            be_bytes_to_u64!(bytes[24..]),
            be_bytes_to_u64!(bytes[32..]),
            be_bytes_to_u64!(bytes[40..]),
            be_bytes_to_u64!(bytes[48..]),
            be_bytes_to_u64!(bytes[56..]),
            be_bytes_to_u64!(bytes[64..]),
            be_bytes_to_u64!(bytes[72..]),
            be_bytes_to_u64!(bytes[80..]),
            be_bytes_to_u64!(bytes[88..]),
        ])
    }

    /// Reduces a big-endian 64-bit limb representation of a 768-bit number.
    fn from_u768(limbs: [u64; 12]) -> Self {
        // We reduce an arbitrary 768-bit number by decomposing it into two 384-bit digits
        // with the higher bits multiplied by 2^384. Thus, we perform two reductions
        //
        // 1. the lower bits are multiplied by R^2, as normal
        // 2. the upper bits are multiplied by R^2 * 2^384 = R^3
        //
        // and computing their sum in the field. It remains to see that arbitrary 384-bit
        // numbers can be placed into Montgomery form safely using the reduction. The
        // reduction works so long as the product is less than R=2^384 multiplied by
        // the modulus. This holds because for any `c` smaller than the modulus, we have
        // that (2^384 - 1)*c is an acceptable product for the reduction. Therefore, the
        // reduction always works so long as `c` is in the field; in this case it is either the
        // constant `R2` or `R3`.
        let d1 = Self([limbs[11], limbs[10], limbs[9], limbs[8], limbs[7], limbs[6]]);
        let d0 = Self([limbs[5], limbs[4], limbs[3], limbs[2], limbs[1], limbs[0]]);
        // Convert to Montgomery form
        (d0.mul_unreduced(&Fp(R2.0)) + d1.mul_unreduced(&Fp(R3.0))).montgomery_reduce().reduce_full()
    }

    /// Returns whether or not this element is strictly lexicographically
    /// larger than its negation.
    pub const fn lexicographically_largest_vartime(&self) -> bool {
        // This can be determined by checking to see if the element is
        // larger than (p - 1) // 2. If we subtract by ((p - 1) // 2) + 1
        // and there is no underflow, then the element must be larger than
        // (p - 1) // 2.

        // First, because self is in Montgomery form we need to reduce it
        let tmp = self.montgomery_reduce();

        let (_, borrow) = borrowing_sub(tmp[0], 0xdcff_7fff_ffff_d556, false);
        let (_, borrow) = borrowing_sub(tmp[1], 0x0f55_ffff_58a9_ffff, borrow);
        let (_, borrow) = borrowing_sub(tmp[2], 0xb398_6950_7b58_7b12, borrow);
        let (_, borrow) = borrowing_sub(tmp[3], 0xb23b_a5c2_79c2_895f, borrow);
        let (_, borrow) = borrowing_sub(tmp[4], 0x258d_d3db_21a5_d66b, borrow);
        let (_, borrow) = borrowing_sub(tmp[5], 0x0d00_88f5_1cbf_f34d, borrow);

        // If the element was smaller, the subtraction will underflow
        // producing a borrow value of 0xffff...ffff, otherwise it will
        // be zero. We create a Choice representing true if there was
        // overflow (and so this element is not lexicographically larger
        // than its negation) and then negate it.
        !borrow
    }

    /// Returns whether or not this element is strictly lexicographically
    /// larger than its negation.
    pub fn lexicographically_largest(&self) -> Choice {
        Choice::from(self.lexicographically_largest_vartime() as u8)
    }

    #[inline]
    pub const fn mul_unreduced(&self, rhs: &Self) -> FpWide<0, VARTIME> {
        FpWide::from_mul(self, rhs)
    }
}

#[cfg(test)]
pub mod test {
    use rand_core::{RngCore, SeedableRng};
    use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

    use crate::util::{FpMag, ConstTime};

    use super::{Fp, FpA, MODULUS};

    pub fn gen_big(mut rng: impl RngCore) -> Fp {
        let mut v = MODULUS;
        v[0] -= 1 + (rng.next_u64() & (1024 - 1));
        Fp(v)
    }
    pub fn gen_big_a(mut rng: impl RngCore) -> FpA {
        let mut v = MODULUS;
        v[0] -= 1 + (rng.next_u64() & (1024 - 1));
        FpA::from_raw_unchecked(v)
    }
    pub fn gen_big_both(mut rng: impl RngCore) -> (Fp, FpA) {
        let mut v = MODULUS;
        v[0] -= 1 + (rng.next_u64() & (1024 - 1));
        (Fp(v), FpA::from_raw_unchecked(v))
    }

    #[test]
    fn test_montgomery_reduce_limit() {
        use rand_core::SeedableRng;
        let mut rng = rand_xorshift::XorShiftRng::from_seed([
            0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        for _ in 0..1_000_000 {
            let a = gen_big(&mut rng);
            let mut v = a.montgomery_reduce();
            let mut modulus = MODULUS;
            v.reverse();
            modulus.reverse();
            assert!(v < modulus, "{v:?} >= {modulus:?}");
        }
        for _ in 0..1_000_000 {
            let a: Fp = Fp::random(&mut rng);
            let mut v = a.montgomery_reduce();
            let mut modulus = MODULUS;
            v.reverse();
            modulus.reverse();
            assert!(v < modulus, "{v:?} >= {modulus:?}");
        }
    }

    #[test]
    fn test_montgomery_reduce_limit_a() {
        let mut rng = rand_xorshift::XorShiftRng::from_seed([
            0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        for _ in 0..1_000_000 {
            let a = gen_big_a(&mut rng);
            let mut v = a.montgomery_reduce();
            let mut modulus = MODULUS;
            v.reverse();
            modulus.reverse();
            assert!(v < modulus, "{v:?} >= {modulus:?}");
        }
        for _ in 0..1_000_000 {
            let a: FpA = FpA::random(&mut rng);
            let mut v = a.montgomery_reduce();
            let mut modulus = MODULUS;
            v.reverse();
            modulus.reverse();
            assert!(v < modulus, "{v:?} >= {modulus:?}");
        }
    }

    #[test]
    fn test_conditional_selection() {
        let a = Fp::<0, false>([1, 2, 3, 4, 5, 6]);
        let b = Fp::<0, false>([7, 8, 9, 10, 11, 12]);

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
    fn test_conditional_selection_a() {
        let a: FpA = FpA::from_raw_unchecked([1, 2, 3, 4, 5, 6]);
        let b: FpA = FpA::from_raw_unchecked([7, 8, 9, 10, 11, 12]);

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
        fn is_equal(a: &Fp, b: &Fp) -> bool {
            let eq = a == b;
            let ct_eq = a.ct_eq(&b);

            assert_eq!(eq, bool::from(ct_eq));

            eq
        }

        assert!(is_equal(&Fp([1, 2, 3, 4, 5, 6]), &Fp([1, 2, 3, 4, 5, 6])));

        assert!(!is_equal(&Fp([7, 2, 3, 4, 5, 6]), &Fp([1, 2, 3, 4, 5, 6])));
        assert!(!is_equal(&Fp([1, 7, 3, 4, 5, 6]), &Fp([1, 2, 3, 4, 5, 6])));
        assert!(!is_equal(&Fp([1, 2, 7, 4, 5, 6]), &Fp([1, 2, 3, 4, 5, 6])));
        assert!(!is_equal(&Fp([1, 2, 3, 7, 5, 6]), &Fp([1, 2, 3, 4, 5, 6])));
        assert!(!is_equal(&Fp([1, 2, 3, 4, 7, 6]), &Fp([1, 2, 3, 4, 5, 6])));
        assert!(!is_equal(&Fp([1, 2, 3, 4, 5, 7]), &Fp([1, 2, 3, 4, 5, 6])));
    }

    #[test]
    fn test_equality_a() {
        fn is_equal(a: &FpA, b: &FpA) -> bool {
            let eq = a == b;
            let ct_eq = a.ct_eq(&b);

            assert_eq!(eq, bool::from(ct_eq));

            eq
        }

        assert!(is_equal(&FpA::from_raw_unchecked([1, 2, 3, 4, 5, 6]), &FpA::from_raw_unchecked([1, 2, 3, 4, 5, 6])));

        assert!(!is_equal(&FpA::from_raw_unchecked([7, 2, 3, 4, 5, 6]), &FpA::from_raw_unchecked([1, 2, 3, 4, 5, 6])));
        assert!(!is_equal(&FpA::from_raw_unchecked([1, 7, 3, 4, 5, 6]), &FpA::from_raw_unchecked([1, 2, 3, 4, 5, 6])));
        assert!(!is_equal(&FpA::from_raw_unchecked([1, 2, 7, 4, 5, 6]), &FpA::from_raw_unchecked([1, 2, 3, 4, 5, 6])));
        assert!(!is_equal(&FpA::from_raw_unchecked([1, 2, 3, 7, 5, 6]), &FpA::from_raw_unchecked([1, 2, 3, 4, 5, 6])));
        assert!(!is_equal(&FpA::from_raw_unchecked([1, 2, 3, 4, 7, 6]), &FpA::from_raw_unchecked([1, 2, 3, 4, 5, 6])));
        assert!(!is_equal(&FpA::from_raw_unchecked([1, 2, 3, 4, 5, 7]), &FpA::from_raw_unchecked([1, 2, 3, 4, 5, 6])));
    }

    #[test]
    fn test_squaring() {
        let a: Fp = Fp([
            0xd215_d276_8e83_191b,
            0x5085_d80f_8fb2_8261,
            0xce9a_032d_df39_3a56,
            0x3e9c_4fff_2ca0_c4bb,
            0x6436_b6f7_f4d9_5dfb,
            0x1060_6628_ad4a_4d90,
        ]);
        let b = Fp([
            0x33d9_c42a_3cb3_e235,
            0xdad1_1a09_4c4c_d455,
            0xa2f1_44bd_729a_aeba,
            0xd415_0932_be9f_feac,
            0xe27b_c7c4_7d44_ee50,
            0x14b6_a78d_3ec7_a560,
        ]);

        assert_eq!(a.square(), b);
    }

    #[test]
    fn test_squaring_a() {
        let a: FpA = FpA::from_raw_unchecked([
            0xd215_d276_8e83_191b,
            0x5085_d80f_8fb2_8261,
            0xce9a_032d_df39_3a56,
            0x3e9c_4fff_2ca0_c4bb,
            0x6436_b6f7_f4d9_5dfb,
            0x1060_6628_ad4a_4d90,
        ]);
        let b: FpA = FpA::from_raw_unchecked([
            0x33d9_c42a_3cb3_e235,
            0xdad1_1a09_4c4c_d455,
            0xa2f1_44bd_729a_aeba,
            0xd415_0932_be9f_feac,
            0xe27b_c7c4_7d44_ee50,
            0x14b6_a78d_3ec7_a560,
        ]);
        assert_eq!(a.square().montgomery_reduce().mag(), b);

        let mut rng = rand_xorshift::XorShiftRng::from_seed([
            0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        for i in 0..1_000 {
            let a = gen_big_a(&mut rng);
            assert_eq!(a.square(), a.mul(&a), "{i}");
        }
        for i in 0..1_000_000 {
            let a: FpA = FpA::random(&mut rng);
            assert_eq!(a.square(), a.mul(&a), "{i}");
        }
    }

    #[test]
    fn test_multiplication() {
        let a: Fp = Fp([
            0x0397_a383_2017_0cd4,
            0x734c_1b2c_9e76_1d30,
            0x5ed2_55ad_9a48_beb5,
            0x095a_3c6b_22a7_fcfc,
            0x2294_ce75_d4e2_6a27,
            0x1333_8bd8_7001_1ebb,
        ]);
        let b = Fp([
            0xb9c3_c7c5_b119_6af7,
            0x2580_e208_6ce3_35c1,
            0xf49a_ed3d_8a57_ef42,
            0x41f2_81e4_9846_e878,
            0xe076_2346_c384_52ce,
            0x0652_e893_26e5_7dc0,
        ]);
        let c = Fp([
            0xf96e_f3d7_11ab_5355,
            0xe8d4_59ea_00f1_48dd,
            0x53f7_354a_5f00_fa78,
            0x9e34_a4f3_125c_5f83,
            0x3fbe_0c47_ca74_c19e,
            0x01b0_6a8b_bd4a_dfe4,
        ]);

        assert_eq!(a * b, c);
    }

    #[test]
    fn test_multiplication_a() {
        let a: FpA = FpA::from_raw_unchecked([
            0x0397_a383_2017_0cd4,
            0x734c_1b2c_9e76_1d30,
            0x5ed2_55ad_9a48_beb5,
            0x095a_3c6b_22a7_fcfc,
            0x2294_ce75_d4e2_6a27,
            0x1333_8bd8_7001_1ebb,
        ]);
        let b: FpA = FpA::from_raw_unchecked([
            0xb9c3_c7c5_b119_6af7,
            0x2580_e208_6ce3_35c1,
            0xf49a_ed3d_8a57_ef42,
            0x41f2_81e4_9846_e878,
            0xe076_2346_c384_52ce,
            0x0652_e893_26e5_7dc0,
        ]);
        let c = FpA::from_raw_unchecked([
            0xf96e_f3d7_11ab_5355,
            0xe8d4_59ea_00f1_48dd,
            0x53f7_354a_5f00_fa78,
            0x9e34_a4f3_125c_5f83,
            0x3fbe_0c47_ca74_c19e,
            0x01b0_6a8b_bd4a_dfe4,
        ]);

        assert_eq!(a.mul(&b).montgomery_reduce(), c);
    }

    #[test]
    fn test_sum_of_squares() {
        let a: Fp = Fp([
            0x5360_bb59_7867_8032,
            0x7dd2_75ae_799e_128e,
            0x5c5b_5071_ce4f_4dcf,
            0xcdb2_1f93_078d_bb3e,
            0xc323_65c5_e73f_474a,
            0x115a_2a54_89ba_be5b,
        ]);
        let b: Fp = Fp([
            0x9fd2_8773_3d23_dda0,
            0xb16b_f2af_738b_3554,
            0x3e57_a75b_d3cc_6d1d,
            0x900b_c0bd_627f_d6d6,
            0xd319_a080_efb2_45fe,
            0x15fd_caa4_e4bb_2091,
        ]);
        let c: Fp = Fp([
            0x3934_42cc_b58b_b327,
            0x1092_685f_3bd5_47e3,
            0x3382_252c_ab6a_c4c9,
            0xf946_94cb_7688_7f55,
            0x4b21_5e90_93a5_e071,
            0x0d56_e30f_34f5_f853,
        ]);

        assert_eq!(Fp::sum_of_squares([a]), a.square());
        assert_eq!(Fp::sum_of_squares([a, b]), a.square() + b.square());
        assert_eq!(Fp::sum_of_squares([a, b, c]), a.square() + b.square() + c.square());
    }

    #[test]
    fn test_addition() {
        let a = Fp::<0>([
            0x5360_bb59_7867_8032,
            0x7dd2_75ae_799e_128e,
            0x5c5b_5071_ce4f_4dcf,
            0xcdb2_1f93_078d_bb3e,
            0xc323_65c5_e73f_474a,
            0x115a_2a54_89ba_be5b,
        ]);
        let b = Fp([
            0x9fd2_8773_3d23_dda0,
            0xb16b_f2af_738b_3554,
            0x3e57_a75b_d3cc_6d1d,
            0x900b_c0bd_627f_d6d6,
            0xd319_a080_efb2_45fe,
            0x15fd_caa4_e4bb_2091,
        ]);
        let c = Fp([
            0x3934_42cc_b58b_b327,
            0x1092_685f_3bd5_47e3,
            0x3382_252c_ab6a_c4c9,
            0xf946_94cb_7688_7f55,
            0x4b21_5e90_93a5_e071,
            0x0d56_e30f_34f5_f853,
        ]);

        assert_eq!(a + b, c);
    }

    #[test]
    fn test_addition_a() {
        let a: FpA = FpA::from_raw_unchecked([
            0x5360_bb59_7867_8032,
            0x7dd2_75ae_799e_128e,
            0x5c5b_5071_ce4f_4dcf,
            0xcdb2_1f93_078d_bb3e,
            0xc323_65c5_e73f_474a,
            0x115a_2a54_89ba_be5b,
        ]);
        let b: FpA = FpA::from_raw_unchecked([
            0x9fd2_8773_3d23_dda0,
            0xb16b_f2af_738b_3554,
            0x3e57_a75b_d3cc_6d1d,
            0x900b_c0bd_627f_d6d6,
            0xd319_a080_efb2_45fe,
            0x15fd_caa4_e4bb_2091,
        ]);
        let c: FpA = FpA::from_raw_unchecked([
            0x3934_42cc_b58b_b327,
            0x1092_685f_3bd5_47e3,
            0x3382_252c_ab6a_c4c9,
            0xf946_94cb_7688_7f55,
            0x4b21_5e90_93a5_e071,
            0x0d56_e30f_34f5_f853,
        ]);

        assert_eq!(a.add(&b).mag(), c);
    }

    #[test]
    fn test_subtraction() {
        let a = Fp::<0>([
            0x5360_bb59_7867_8032,
            0x7dd2_75ae_799e_128e,
            0x5c5b_5071_ce4f_4dcf,
            0xcdb2_1f93_078d_bb3e,
            0xc323_65c5_e73f_474a,
            0x115a_2a54_89ba_be5b,
        ]);
        let b = Fp([
            0x9fd2_8773_3d23_dda0,
            0xb16b_f2af_738b_3554,
            0x3e57_a75b_d3cc_6d1d,
            0x900b_c0bd_627f_d6d6,
            0xd319_a080_efb2_45fe,
            0x15fd_caa4_e4bb_2091,
        ]);
        let c = Fp([
            0x6d8d_33e6_3b43_4d3d,
            0xeb12_82fd_b766_dd39,
            0x8534_7bb6_f133_d6d5,
            0xa21d_aa5a_9892_f727,
            0x3b25_6cfb_3ad8_ae23,
            0x155d_7199_de7f_8464,
        ]);

        assert_eq!(a - b, c);
    }

    #[test]
    fn test_subtraction_a() {
        let a: FpA = FpA::from_raw_unchecked([
            0x5360_bb59_7867_8032,
            0x7dd2_75ae_799e_128e,
            0x5c5b_5071_ce4f_4dcf,
            0xcdb2_1f93_078d_bb3e,
            0xc323_65c5_e73f_474a,
            0x115a_2a54_89ba_be5b,
        ]);
        let b: FpA = FpA::from_raw_unchecked([
            0x9fd2_8773_3d23_dda0,
            0xb16b_f2af_738b_3554,
            0x3e57_a75b_d3cc_6d1d,
            0x900b_c0bd_627f_d6d6,
            0xd319_a080_efb2_45fe,
            0x15fd_caa4_e4bb_2091,
        ]);
        let c: FpA = FpA::from_raw_unchecked([
            0x6d8d_33e6_3b43_4d3d,
            0xeb12_82fd_b766_dd39,
            0x8534_7bb6_f133_d6d5,
            0xa21d_aa5a_9892_f727,
            0x3b25_6cfb_3ad8_ae23,
            0x155d_7199_de7f_8464,
        ]);

        assert_eq!(a.sub(&b), c);
    }

    #[test]
    fn test_negation() {
        let a = Fp::<0, false>([
            0x5360_bb59_7867_8032,
            0x7dd2_75ae_799e_128e,
            0x5c5b_5071_ce4f_4dcf,
            0xcdb2_1f93_078d_bb3e,
            0xc323_65c5_e73f_474a,
            0x115a_2a54_89ba_be5b,
        ]);
        let b = Fp([
            0x669e_44a6_8798_2a79,
            0xa0d9_8a50_37b5_ed71,
            0x0ad5_822f_2861_a854,
            0x96c5_2bf1_ebf7_5781,
            0x87f8_41f0_5c0c_658c,
            0x08a6_e795_afc5_283e,
        ]);

        assert_eq!(-a, b);
    }

    #[test]
    fn test_negation_a() {
        let a: FpA = FpA::from_raw_unchecked([
            0x5360_bb59_7867_8032,
            0x7dd2_75ae_799e_128e,
            0x5c5b_5071_ce4f_4dcf,
            0xcdb2_1f93_078d_bb3e,
            0xc323_65c5_e73f_474a,
            0x115a_2a54_89ba_be5b,
        ]);
        let b: FpA = FpA::from_raw_unchecked([
            0x669e_44a6_8798_2a79,
            0xa0d9_8a50_37b5_ed71,
            0x0ad5_822f_2861_a854,
            0x96c5_2bf1_ebf7_5781,
            0x87f8_41f0_5c0c_658c,
            0x08a6_e795_afc5_283e,
        ]);

        assert_eq!(a.neg(), b);
    }


    #[test]
    fn test_pow_a() {
        let mut rng = rand_xorshift::XorShiftRng::from_seed([
            0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        for i in 0..10_000 {
            let (v, va) = gen_big_both(&mut rng);
            let p = [(); 6].map(|_| rng.next_u64());
            assert_eq!(v.pow_vartime(&p).0, v.pow_vartime(&p).0, "{i}");
        }
    }

    #[test]
    fn test_debug() {
        assert_eq!(
            format!(
                "{:?}",
                Fp::<0>([
                    0x5360_bb59_7867_8032,
                    0x7dd2_75ae_799e_128e,
                    0x5c5b_5071_ce4f_4dcf,
                    0xcdb2_1f93_078d_bb3e,
                    0xc323_65c5_e73f_474a,
                    0x115a_2a54_89ba_be5b,
                ])
            ),
            "0x104bf052ad3bc99bcb176c24a06a6c3aad4eaf2308fc4d282e106c84a757d061052630515305e59bdddf8111bfdeb704"
        );
    }

    #[test]
    fn test_debug_a() {
        assert_eq!(
            format!(
                "{:?}",
                FpA::<FpMag<0>, ConstTime>::from_raw_unchecked([
                    0x5360_bb59_7867_8032,
                    0x7dd2_75ae_799e_128e,
                    0x5c5b_5071_ce4f_4dcf,
                    0xcdb2_1f93_078d_bb3e,
                    0xc323_65c5_e73f_474a,
                    0x115a_2a54_89ba_be5b,
                ])
            ),
            "0x104bf052ad3bc99bcb176c24a06a6c3aad4eaf2308fc4d282e106c84a757d061052630515305e59bdddf8111bfdeb704"
        );
    }

    #[test]
    fn test_from_bytes() {
        let mut a = Fp::<0>([
            0xdc90_6d9b_e3f9_5dc8,
            0x8755_caf7_4596_91a1,
            0xcff1_a7f4_e958_3ab3,
            0x9b43_821f_849e_2284,
            0xf575_54f3_a297_4f3f,
            0x085d_bea8_4ed4_7f79,
        ]);

        for _ in 0..100 {
            a = a.square();
            let tmp = a.to_bytes();
            let b = Fp::from_bytes(&tmp).unwrap();

            assert_eq!(a, b);
        }

        assert_eq!(
            -Fp::<0, false>::one(),
            Fp::from_bytes(&[
                26, 1, 17, 234, 57, 127, 230, 154, 75, 27, 167, 182, 67, 75, 172, 215, 100, 119,
                75, 132, 243, 133, 18, 191, 103, 48, 210, 160, 246, 176, 246, 36, 30, 171, 255,
                254, 177, 83, 255, 255, 185, 254, 255, 255, 255, 255, 170, 170
            ])
            .unwrap()
        );

        assert!(bool::from(
            Fp::<0, false>::from_bytes(&[
                27, 1, 17, 234, 57, 127, 230, 154, 75, 27, 167, 182, 67, 75, 172, 215, 100, 119,
                75, 132, 243, 133, 18, 191, 103, 48, 210, 160, 246, 176, 246, 36, 30, 171, 255,
                254, 177, 83, 255, 255, 185, 254, 255, 255, 255, 255, 170, 170
            ])
            .is_none()
        ));

        assert!(bool::from(Fp::<0, false>::from_bytes(&[0xff; 48]).is_none()));
    }

    #[test]
    fn test_from_bytes_a() {
        let mut a: FpA = FpA::from_raw_unchecked([
            0xdc90_6d9b_e3f9_5dc8,
            0x8755_caf7_4596_91a1,
            0xcff1_a7f4_e958_3ab3,
            0x9b43_821f_849e_2284,
            0xf575_54f3_a297_4f3f,
            0x085d_bea8_4ed4_7f79,
        ]);

        for _ in 0..100 {
            let tmp = a.to_bytes();
            let b = FpA::from_bytes(&tmp).unwrap();
            assert_eq!(a, b);
            a = a.square().montgomery_reduce().mag();
        }

        assert_eq!(
            FpA::<FpMag<0>, ConstTime>::one().neg(),
            FpA::from_bytes(&[
                26, 1, 17, 234, 57, 127, 230, 154, 75, 27, 167, 182, 67, 75, 172, 215, 100, 119,
                75, 132, 243, 133, 18, 191, 103, 48, 210, 160, 246, 176, 246, 36, 30, 171, 255,
                254, 177, 83, 255, 255, 185, 254, 255, 255, 255, 255, 170, 170
            ])
            .unwrap()
        );

        assert!(bool::from(
            FpA::<FpMag<0>, ConstTime>::from_bytes(&[
                27, 1, 17, 234, 57, 127, 230, 154, 75, 27, 167, 182, 67, 75, 172, 215, 100, 119,
                75, 132, 243, 133, 18, 191, 103, 48, 210, 160, 246, 176, 246, 36, 30, 171, 255,
                254, 177, 83, 255, 255, 185, 254, 255, 255, 255, 255, 170, 170
            ])
            .is_none()
        ));

        assert!(bool::from(FpA::<FpMag<0>, ConstTime>::from_bytes(&[0xff; 48]).is_none()));
    }

    #[test]
    fn test_sqrt() {
        // a = 4
        let a: Fp = Fp::from_raw_unchecked([
            0xaa27_0000_000c_fff3,
            0x53cc_0032_fc34_000a,
            0x478f_e97a_6b0a_807f,
            0xb1d3_7ebe_e6ba_24d7,
            0x8ec9_733b_bf78_ab2f,
            0x09d6_4551_3d83_de7e,
        ]);

        assert_eq!(
            // sqrt(4) = -2
            -a.sqrt().unwrap(),
            // 2
            Fp::from_raw_unchecked([
                0x3213_0000_0006_554f,
                0xb93c_0018_d6c4_0005,
                0x5760_5e0d_b0dd_bb51,
                0x8b25_6521_ed1f_9bcb,
                0x6cf2_8d79_0162_2c03,
                0x11eb_ab9d_bb81_e28c,
            ])
        );
    }

    #[test]
    fn test_sqrt_a() {
        // a = 4
        let a: FpA = FpA::from_raw_unchecked([
            0xaa27_0000_000c_fff3,
            0x53cc_0032_fc34_000a,
            0x478f_e97a_6b0a_807f,
            0xb1d3_7ebe_e6ba_24d7,
            0x8ec9_733b_bf78_ab2f,
            0x09d6_4551_3d83_de7e,
        ]);

        assert_eq!(
            // sqrt(4) = -2
            a.sqrt().unwrap().neg().mag(),
            // 2
            FpA::<FpMag<0>, ConstTime>::from_raw_unchecked([
                0x3213_0000_0006_554f,
                0xb93c_0018_d6c4_0005,
                0x5760_5e0d_b0dd_bb51,
                0x8b25_6521_ed1f_9bcb,
                0x6cf2_8d79_0162_2c03,
                0x11eb_ab9d_bb81_e28c,
            ])
        );
    }

    #[test]
    fn test_inversion() {
        let a: Fp = Fp([
            0x43b4_3a50_78ac_2076,
            0x1ce0_7630_46f8_962b,
            0x724a_5276_486d_735c,
            0x6f05_c2a6_282d_48fd,
            0x2095_bd5b_b4ca_9331,
            0x03b3_5b38_94b0_f7da,
        ]);
        let b = Fp([
            0x69ec_d704_0952_148f,
            0x985c_cc20_2219_0f55,
            0xe19b_ba36_a9ad_2f41,
            0x19bb_16c9_5219_dbd8,
            0x14dc_acfd_fb47_8693,
            0x115f_f58a_fff9_a8e1,
        ]);

        assert_eq!(a.invert().unwrap(), b);
        assert!(bool::from(Fp::<0, false>::zero().invert().is_none()));
    }

    #[test]
    fn test_inversion_a() {
        let a: FpA = FpA::from_raw_unchecked([
            0x43b4_3a50_78ac_2076,
            0x1ce0_7630_46f8_962b,
            0x724a_5276_486d_735c,
            0x6f05_c2a6_282d_48fd,
            0x2095_bd5b_b4ca_9331,
            0x03b3_5b38_94b0_f7da,
        ]);
        let b: FpA = FpA::from_raw_unchecked([
            0x69ec_d704_0952_148f,
            0x985c_cc20_2219_0f55,
            0xe19b_ba36_a9ad_2f41,
            0x19bb_16c9_5219_dbd8,
            0x14dc_acfd_fb47_8693,
            0x115f_f58a_fff9_a8e1,
        ]);

        assert_eq!(a.invert().unwrap().mag(), b);
        assert!(bool::from(FpA::<FpMag<0>, ConstTime>::zero().invert().is_none()));
    }

    #[test]
    fn test_lexicographic_largest() {
        assert!(!bool::from(Fp::<0, false>::zero().lexicographically_largest()));
        assert!(!bool::from(Fp::<0, false>::one().lexicographically_largest()));
        assert!(!bool::from(
            Fp::<0, false>::from_raw_unchecked([
                0xa1fa_ffff_fffe_5557,
                0x995b_fff9_76a3_fffe,
                0x03f4_1d24_d174_ceb4,
                0xf654_7998_c199_5dbd,
                0x778a_468f_507a_6034,
                0x0205_5993_1f7f_8103
            ])
            .lexicographically_largest()
        ));
        assert!(bool::from(
            Fp::<0, false>::from_raw_unchecked([
                0x1804_0000_0001_5554,
                0x8550_0005_3ab0_0001,
                0x633c_b57c_253c_276f,
                0x6e22_d1ec_31eb_b502,
                0xd391_6126_f2d1_4ca2,
                0x17fb_b857_1a00_6596,
            ])
            .lexicographically_largest()
        ));
        assert!(bool::from(
            Fp::<0, false>::from_raw_unchecked([
                0x43f5_ffff_fffc_aaae,
                0x32b7_fff2_ed47_fffd,
                0x07e8_3a49_a2e9_9d69,
                0xeca8_f331_8332_bb7a,
                0xef14_8d1e_a0f4_c069,
                0x040a_b326_3eff_0206,
            ])
            .lexicographically_largest()
        ));
    }

    #[cfg(feature = "zeroize")]
    #[test]
    fn test_zeroize() {
        use zeroize::Zeroize;

        let mut a: Fp = Fp::one();
        a.zeroize();
        assert!(bool::from(a.is_zero()));
    }

    #[cfg(feature = "zeroize")]
    #[test]
    fn test_zeroize_a() {
        use zeroize::Zeroize;

        let mut a: FpA = FpA::one();
        a.zeroize();
        assert!(bool::from(a.is_zero()));
    }
}
