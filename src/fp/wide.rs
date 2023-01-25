use core::ops::{Add, Sub};

use crate::{
    fp::Fp,
    util::{adc, mac, sbb, slc},
};

#[inline(always)]
/// The return value is bounded by $(mp^2 + Rp − p) / R$
/// where $mp^2$ is the modulus of `v`. This means `m` must be 87 or lower, as
/// a value 88 or higher would result in overflow.
pub const fn montgomery_reduce_wide(v: &[u64; 12]) -> [u64; 6] {
    use super::{INV, MODULUS};

    // The Montgomery reduction here is based on Algorithm 14.32 in
    // Handbook of Applied Cryptography
    // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.
    let [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11] = *v;

    let k = t0.wrapping_mul(INV);
    let (_, carry) = mac(t0, k, MODULUS[0], 0);
    let (r1, carry) = mac(t1, k, MODULUS[1], carry);
    let (r2, carry) = mac(t2, k, MODULUS[2], carry);
    let (r3, carry) = mac(t3, k, MODULUS[3], carry);
    let (r4, carry) = mac(t4, k, MODULUS[4], carry);
    let (r5, carry) = mac(t5, k, MODULUS[5], carry);
    let (r6, r7) = adc(t6, 0, carry);

    let k = r1.wrapping_mul(INV);
    let (_, carry) = mac(r1, k, MODULUS[0], 0);
    let (r2, carry) = mac(r2, k, MODULUS[1], carry);
    let (r3, carry) = mac(r3, k, MODULUS[2], carry);
    let (r4, carry) = mac(r4, k, MODULUS[3], carry);
    let (r5, carry) = mac(r5, k, MODULUS[4], carry);
    let (r6, carry) = mac(r6, k, MODULUS[5], carry);
    let (r7, r8) = adc(t7, r7, carry);

    let k = r2.wrapping_mul(INV);
    let (_, carry) = mac(r2, k, MODULUS[0], 0);
    let (r3, carry) = mac(r3, k, MODULUS[1], carry);
    let (r4, carry) = mac(r4, k, MODULUS[2], carry);
    let (r5, carry) = mac(r5, k, MODULUS[3], carry);
    let (r6, carry) = mac(r6, k, MODULUS[4], carry);
    let (r7, carry) = mac(r7, k, MODULUS[5], carry);
    let (r8, r9) = adc(t8, r8, carry);

    let k = r3.wrapping_mul(INV);
    let (_, carry) = mac(r3, k, MODULUS[0], 0);
    let (r4, carry) = mac(r4, k, MODULUS[1], carry);
    let (r5, carry) = mac(r5, k, MODULUS[2], carry);
    let (r6, carry) = mac(r6, k, MODULUS[3], carry);
    let (r7, carry) = mac(r7, k, MODULUS[4], carry);
    let (r8, carry) = mac(r8, k, MODULUS[5], carry);
    let (r9, r10) = adc(t9, r9, carry);

    let k = r4.wrapping_mul(INV);
    let (_, carry) = mac(r4, k, MODULUS[0], 0);
    let (r5, carry) = mac(r5, k, MODULUS[1], carry);
    let (r6, carry) = mac(r6, k, MODULUS[2], carry);
    let (r7, carry) = mac(r7, k, MODULUS[3], carry);
    let (r8, carry) = mac(r8, k, MODULUS[4], carry);
    let (r9, carry) = mac(r9, k, MODULUS[5], carry);
    let (r10, r11) = adc(t10, r10, carry);

    let k = r5.wrapping_mul(INV);
    let (_, carry) = mac(r5, k, MODULUS[0], 0);
    let (r6, carry) = mac(r6, k, MODULUS[1], carry);
    let (r7, carry) = mac(r7, k, MODULUS[2], carry);
    let (r8, carry) = mac(r8, k, MODULUS[3], carry);
    let (r9, carry) = mac(r9, k, MODULUS[4], carry);
    let (r10, carry) = mac(r10, k, MODULUS[5], carry);
    let (r11, _carry) = adc(t11, r11, carry);

    // The caller must attempt to subtract the modulus, to ensure the value
    // is smaller than the modulus
    [r6, r7, r8, r9, r10, r11]
}

#[inline]
const fn mul_wide(lhs: &[u64; 6], rhs: &[u64; 6]) -> [u64; 12] {
    let (t0, carry) = mac(0, lhs[0], rhs[0], 0);
    let (t1, carry) = mac(0, lhs[0], rhs[1], carry);
    let (t2, carry) = mac(0, lhs[0], rhs[2], carry);
    let (t3, carry) = mac(0, lhs[0], rhs[3], carry);
    let (t4, carry) = mac(0, lhs[0], rhs[4], carry);
    let (t5, t6) = mac(0, lhs[0], rhs[5], carry);

    let (t1, carry) = mac(t1, lhs[1], rhs[0], 0);
    let (t2, carry) = mac(t2, lhs[1], rhs[1], carry);
    let (t3, carry) = mac(t3, lhs[1], rhs[2], carry);
    let (t4, carry) = mac(t4, lhs[1], rhs[3], carry);
    let (t5, carry) = mac(t5, lhs[1], rhs[4], carry);
    let (t6, t7) = mac(t6, lhs[1], rhs[5], carry);

    let (t2, carry) = mac(t2, lhs[2], rhs[0], 0);
    let (t3, carry) = mac(t3, lhs[2], rhs[1], carry);
    let (t4, carry) = mac(t4, lhs[2], rhs[2], carry);
    let (t5, carry) = mac(t5, lhs[2], rhs[3], carry);
    let (t6, carry) = mac(t6, lhs[2], rhs[4], carry);
    let (t7, t8) = mac(t7, lhs[2], rhs[5], carry);

    let (t3, carry) = mac(t3, lhs[3], rhs[0], 0);
    let (t4, carry) = mac(t4, lhs[3], rhs[1], carry);
    let (t5, carry) = mac(t5, lhs[3], rhs[2], carry);
    let (t6, carry) = mac(t6, lhs[3], rhs[3], carry);
    let (t7, carry) = mac(t7, lhs[3], rhs[4], carry);
    let (t8, t9) = mac(t8, lhs[3], rhs[5], carry);

    let (t4, carry) = mac(t4, lhs[4], rhs[0], 0);
    let (t5, carry) = mac(t5, lhs[4], rhs[1], carry);
    let (t6, carry) = mac(t6, lhs[4], rhs[2], carry);
    let (t7, carry) = mac(t7, lhs[4], rhs[3], carry);
    let (t8, carry) = mac(t8, lhs[4], rhs[4], carry);
    let (t9, t10) = mac(t9, lhs[4], rhs[5], carry);

    let (t5, carry) = mac(t5, lhs[5], rhs[0], 0);
    let (t6, carry) = mac(t6, lhs[5], rhs[1], carry);
    let (t7, carry) = mac(t7, lhs[5], rhs[2], carry);
    let (t8, carry) = mac(t8, lhs[5], rhs[3], carry);
    let (t9, carry) = mac(t9, lhs[5], rhs[4], carry);
    let (t10, t11) = mac(t10, lhs[5], rhs[5], carry);

    [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]
}

#[inline]
pub const fn square_wide(v: &[u64; 6]) -> [u64; 12] {
    let (t1, carry) = mac(0, v[0], v[1], 0);
    let (t2, carry) = mac(0, v[0], v[2], carry);
    let (t3, carry) = mac(0, v[0], v[3], carry);
    let (t4, carry) = mac(0, v[0], v[4], carry);
    let (t5, t6) = mac(0, v[0], v[5], carry);

    let (t3, carry) = mac(t3, v[1], v[2], 0);
    let (t4, carry) = mac(t4, v[1], v[3], carry);
    let (t5, carry) = mac(t5, v[1], v[4], carry);
    let (t6, t7) = mac(t6, v[1], v[5], carry);

    let (t5, carry) = mac(t5, v[2], v[3], 0);
    let (t6, carry) = mac(t6, v[2], v[4], carry);
    let (t7, t8) = mac(t7, v[2], v[5], carry);

    let (t7, carry) = mac(t7, v[3], v[4], 0);
    let (t8, t9) = mac(t8, v[3], v[5], carry);

    let (t9, t10) = mac(t9, v[4], v[5], 0);

    let t11 = t10 >> 63;
    let t10 = (t10 << 1) | (t9 >> 63);
    let t9 = (t9 << 1) | (t8 >> 63);
    let t8 = (t8 << 1) | (t7 >> 63);
    let t7 = (t7 << 1) | (t6 >> 63);
    let t6 = (t6 << 1) | (t5 >> 63);
    let t5 = (t5 << 1) | (t4 >> 63);
    let t4 = (t4 << 1) | (t3 >> 63);
    let t3 = (t3 << 1) | (t2 >> 63);
    let t2 = (t2 << 1) | (t1 >> 63);
    let t1 = t1 << 1;

    let (t0, carry) = mac(0, v[0], v[0], 0);
    let (t1, carry) = adc(t1, 0, carry);
    let (t2, carry) = mac(t2, v[1], v[1], carry);
    let (t3, carry) = adc(t3, 0, carry);
    let (t4, carry) = mac(t4, v[2], v[2], carry);
    let (t5, carry) = adc(t5, 0, carry);
    let (t6, carry) = mac(t6, v[3], v[3], carry);
    let (t7, carry) = adc(t7, 0, carry);
    let (t8, carry) = mac(t8, v[4], v[4], carry);
    let (t9, carry) = adc(t9, 0, carry);
    let (t10, carry) = mac(t10, v[5], v[5], carry);
    let (t11, _) = adc(t11, 0, carry);

    [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11]
}

/// Add two elements.
#[inline]
const fn add_wide(lhs: &[u64; 12], rhs: &[u64; 12]) -> [u64; 12] {
    let (d0, carry) = adc(lhs[0], rhs[0], 0);
    let (d1, carry) = adc(lhs[1], rhs[1], carry);
    let (d2, carry) = adc(lhs[2], rhs[2], carry);
    let (d3, carry) = adc(lhs[3], rhs[3], carry);
    let (d4, carry) = adc(lhs[4], rhs[4], carry);
    let (d5, carry) = adc(lhs[5], rhs[5], carry);
    let (d6, carry) = adc(lhs[6], rhs[6], carry);
    let (d7, carry) = adc(lhs[7], rhs[7], carry);
    let (d8, carry) = adc(lhs[8], rhs[8], carry);
    let (d9, carry) = adc(lhs[9], rhs[9], carry);
    let (d10, carry) = adc(lhs[10], rhs[10], carry);
    let (d11, _carry) = adc(lhs[11], rhs[11], carry);

    [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]
}

#[inline]
pub const fn double_wide(v: &[u64; 12]) -> [u64; 12] {
    let (d0, carry) = slc(v[0], 1, 0);
    let (d1, carry) = slc(v[1], 1, carry);
    let (d2, carry) = slc(v[2], 1, carry);
    let (d3, carry) = slc(v[3], 1, carry);
    let (d4, carry) = slc(v[4], 1, carry);
    let (d5, carry) = slc(v[5], 1, carry);
    let (d6, carry) = slc(v[6], 1, carry);
    let (d7, carry) = slc(v[7], 1, carry);
    let (d8, carry) = slc(v[8], 1, carry);
    let (d9, carry) = slc(v[9], 1, carry);
    let (d10, carry) = slc(v[10], 1, carry);
    let (d11, _carry) = slc(v[11], 1, carry);

    [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]
}

/// Negates an element by subtracting it from the `Self::MODULUS`
#[inline]
const fn negate_wide(v: &[u64; 12], modulus: &[u64; 12]) -> [u64; 12] {
    let (d0, borrow) = sbb(modulus[0], v[0], 0);
    let (d1, borrow) = sbb(modulus[1], v[1], borrow);
    let (d2, borrow) = sbb(modulus[2], v[2], borrow);
    let (d3, borrow) = sbb(modulus[3], v[3], borrow);
    let (d4, borrow) = sbb(modulus[4], v[4], borrow);
    let (d5, borrow) = sbb(modulus[5], v[5], borrow);
    let (d6, borrow) = sbb(modulus[6], v[6], borrow);
    let (d7, borrow) = sbb(modulus[7], v[7], borrow);
    let (d8, borrow) = sbb(modulus[8], v[8], borrow);
    let (d9, borrow) = sbb(modulus[9], v[9], borrow);
    let (d10, borrow) = sbb(modulus[10], v[10], borrow);
    let (d11, _) = sbb(modulus[11], v[11], borrow);

    [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]
}

/// The unreduced result of `Fp` multiplication.
/// The internal representation of this type is twelve 64-bit unsigned
/// integers in little-endian order. `FpWide` values are always in
/// double Montgomery form; i.e., FpWide<M>(a) = a*R^2 mod M*p^2, with R = 2^384.
#[derive(Debug, Clone, Copy)]
pub struct FpWide<const MAGNITUDE: usize>([u64; 12]);

// MAGNITUDE cannot be above 87, or else
impl<const MAGNITUDE: usize> FpWide<MAGNITUDE> {
    #[inline(always)]
    pub const fn montgomery_reduce(self) -> Fp {
        use super::{subtract_p, MODULUS, P2, P4, P8};
        let v = montgomery_reduce_wide(&self.0);

        let v = if MAGNITUDE >= 68 {
            // 68 indicates a mod of 69 p^2
            // when f is bounded by (69 p^2 + Rp − p) / R
            // and 68p/R < 7 < 69 p/R < 8
            // means max(f) > 8p
            subtract_p(&v, &P8)
        } else {
            v
        };

        let v = if MAGNITUDE >= 29 {
            // 29 indicates a mod of 30 p^2
            // when f is bounded by (30 p^2 + Rp − p) / R
            // and 29p/R < 3 < 30 p/R < 4
            // means max(f) > 4p
            subtract_p(&v, &P4)
        } else {
            v
        };

        let v = if MAGNITUDE >= 9 {
            // 9 indicates a mod of 10 p^2
            // when f is bounded by (10 p^2 + Rp − p) / R
            // and 9p/R < 1 < 10p/R < 2
            // means max(f) > 2p
            subtract_p(&v, &P2)
        } else {
            v
        };

        // when f is bounded by (p^2 + Rp − p) / R
        // and p/R < 1
        // means max(f) < 2p
        Fp(subtract_p(&v, &MODULUS))
    }
}

impl FpWide<0> {
    #[inline(always)]
    pub const fn from_mul(lhs: &Fp, rhs: &Fp) -> Self {
        Self(mul_wide(&lhs.0, &rhs.0))
    }

    #[inline(always)]
    pub const fn from_square(v: &Fp) -> Self {
        Self(square_wide(&v.0))
    }
}

// Hack to get the ! type on stable
pub trait HasOutput {
    type Output;
}
impl<O> HasOutput for fn() -> O {
    type Output = O;
}
type Never = <fn() -> ! as HasOutput>::Output;

const MODULUS_INCREMENT: [u64; 12] = square_wide(&super::MODULUS);

pub trait Wide: Sized {
    type Prev: Wide;
    type Next: Wide;

    /// A multiple of the prime that is larger than this element could be (p^2).
    const MODULUS: [u64; 12] = add_wide(&Self::Prev::MODULUS, &MODULUS_INCREMENT);

    fn make(v: [u64; 12]) -> Self;
    fn data(&self) -> &[u64; 12];

    /// Negates an element by subtracting it from the `Self::MODULUS`
    #[inline(always)]
    fn negate(&self) -> Self {
        Self::make(negate_wide(self.data(), &Self::MODULUS))
    }
}

pub trait NonZero {}

impl Wide for Never {
    type Prev = Never;
    type Next = Never;
    const MODULUS: [u64; 12] = [0; 12];

    #[inline(always)]
    fn make(_: [u64; 12]) -> Self {
        unimplemented!()
    }
    #[inline(always)]
    fn data(&self) -> &[u64; 12] {
        unreachable!()
    }
}

macro_rules! wide_impl {
    ($($($ua:literal),+ $(,)?)?) => {$($(
impl Wide for FpWide<$ua> {
    type Prev = FpWide<{$ua - 1}>;
    type Next = FpWide<{$ua + 1}>;

    #[inline(always)]
    fn make(v: [u64; 12]) -> Self {
        FpWide(v)
    }
    #[inline(always)]
    fn data(&self) -> &[u64; 12] {
        &self.0
    }
}

impl NonZero for FpWide<$ua> {}
    )+)?};
}

impl Wide for FpWide<0> {
    type Prev = Never;
    type Next = FpWide<1>;

    #[inline(always)]
    fn make(v: [u64; 12]) -> Self {
        FpWide(v)
    }
    #[inline(always)]
    fn data(&self) -> &[u64; 12] {
        &self.0
    }
}

wide_impl! {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84}
impl Wide for FpWide<85> {
    type Prev = FpWide<84>;
    type Next = Never;

    #[inline(always)]
    fn make(v: [u64; 12]) -> Self {
        FpWide(v)
    }
    #[inline(always)]
    fn data(&self) -> &[u64; 12] {
        &self.0
    }
}

pub trait Ops<const MAG: usize> {
    type OpOut: Wide;
    fn add(lhs: &Self, rhs: &FpWide<MAG>) -> Self::OpOut;
    fn sub(lhs: &Self, rhs: &FpWide<MAG>) -> Self::OpOut;
}

impl<const MAG2: usize> Ops<MAG2> for FpWide<0>
where
    FpWide<MAG2>: Wide,
{
    type OpOut = <FpWide<MAG2> as Wide>::Next;
    #[inline(always)]
    fn add(lhs: &Self, rhs: &FpWide<MAG2>) -> Self::OpOut {
        Wide::make(add_wide(&lhs.0, &rhs.0))
    }
    #[inline(always)]
    fn sub(lhs: &Self, rhs: &FpWide<MAG2>) -> Self::OpOut {
        Wide::make(add_wide(&lhs.0, &rhs.negate().0))
    }
}

impl<const MAG1: usize, const MAG2: usize> Ops<MAG2> for FpWide<MAG1>
where
    FpWide<MAG1>: Wide + NonZero,
    <FpWide<MAG1> as Wide>::Prev: Ops<MAG2>,
    FpWide<MAG2>: Wide,
{
    type OpOut = <<<FpWide<MAG1> as Wide>::Prev as Ops<MAG2>>::OpOut as Wide>::Next;
    #[inline(always)]
    fn add(lhs: &Self, rhs: &FpWide<MAG2>) -> Self::OpOut {
        Wide::make(add_wide(&lhs.0, &rhs.0))
    }
    #[inline(always)]
    fn sub(lhs: &Self, rhs: &FpWide<MAG2>) -> Self::OpOut {
        Wide::make(add_wide(&lhs.0, &(rhs.negate()).0))
    }
}

impl<'a, 'b, const MAG1: usize, const MAG2: usize> Add<&'b FpWide<MAG2>> for &'a FpWide<MAG1>
where
    FpWide<MAG1>: Ops<MAG2>,
{
    type Output = <FpWide<MAG1> as Ops<MAG2>>::OpOut;

    #[inline(always)]
    fn add(self, rhs: &'b FpWide<MAG2>) -> Self::Output {
        Ops::add(self, rhs)
    }
}
impl<'a, 'b, const MAG1: usize, const MAG2: usize> Sub<&'b FpWide<MAG2>> for &'a FpWide<MAG1>
where
    FpWide<MAG1>: Ops<MAG2>,
{
    type Output = <FpWide<MAG1> as Ops<MAG2>>::OpOut;

    #[inline(always)]
    fn sub(self, rhs: &'b FpWide<MAG2>) -> Self::Output {
        Ops::sub(self, rhs)
    }
}

impl_binops_additive_output! {{MAG1 MAG2} {where FpWide<MAG1>: Ops<MAG2>} {FpWide} {FpWide}}

macro_rules! wide_double_impl {
($($($ua:literal),+ $(,)?)?) => {$($(
impl FpWide<$ua> {
    #[inline(always)]
    pub fn double(&self) -> FpWide<{$ua*2 + 1}> {
        FpWide(double_wide(&self.0))
    }
}
)+)?};
}

wide_double_impl! {
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42
}

#[cfg(test)]
mod test {
    use rand_core::RngCore;

    use crate::fp::{
        wide::{add_wide, double_wide, FpWide},
        Fp, MODULUS,
    };

    fn gen_big(mut rng: impl RngCore) -> Fp {
        let mut v = MODULUS;
        v[0] -= 1 + (rng.next_u64() & (1024 - 1));
        Fp(v)
    }

    #[test]
    fn test_depth() {
        use rand_core::SeedableRng;
        let mut rng = rand_xorshift::XorShiftRng::from_seed([
            0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for i in 0..1_000_000 {
            let a = gen_big(&mut rng);
            let b = gen_big(&mut rng);

            let v = a * b;
            let v_ur = a.mul_unreduced(&b);

            let v_5 = v.double().double() + v;
            let v_5_ur = v_ur.double().double() + v_ur;
            assert_eq!(v_5.0, v_5_ur.montgomery_reduce().0);

            let v_10 = v_5.double();
            let v_10_ur = v_5_ur + v_5_ur;
            assert_eq!(v_10.0, v_10_ur.montgomery_reduce().0, "{}", i);

            let v = v.double() + v;
            let v_ur = v_ur.double() + v_ur;
            assert_eq!(v.0, v_ur.montgomery_reduce().0);

            let v = v.double();
            let v_ur = v_ur.double();
            assert_eq!(v.0, v_ur.montgomery_reduce().0);

            let v = v.double();
            let v_ur = v_ur.double();
            assert_eq!(v.0, v_ur.montgomery_reduce().0);

            let v = v.double();
            let v_ur = v_ur.double();
            assert_eq!(v.0, v_ur.montgomery_reduce().0);

            let v = v.double();
            let v_ur = v_ur.double();
            assert_eq!(v.0, v_ur.montgomery_reduce().0);

            let v = v_10.double().double();
            let v_ur = v_10_ur.double().double();
            assert_eq!(v.0, v_ur.montgomery_reduce().0);

            let v = v.double() + v_5;
            let v_ur: FpWide<84> = v_ur.double() + v_5_ur;
            assert_eq!(v, v_ur.montgomery_reduce(), "{}", i);
            assert_eq!(v.0, v_ur.montgomery_reduce().0, "{}", i);
        }
    }

    #[test]
    fn test_double() {
        use rand_core::SeedableRng;
        let mut rng = rand_xorshift::XorShiftRng::from_seed([
            0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);

        for _ in 0..(1000 * 1000) {
            let v = gen_big(&mut rng).mul_unreduced(&gen_big(&mut rng));

            assert_eq!(double_wide(&v.0), add_wide(&v.0, &v.0))
        }
    }

    #[test]
    fn test_add_limit() {
        use rand_core::SeedableRng;
        let mut rng = rand_xorshift::XorShiftRng::from_seed([
            0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        for _ in 0..32 {
            let [a, b, c, d] = [(); 4].map(|_| Fp::random(&mut rng));

            assert_eq!(
                a * b + c * d,
                (a.mul_unreduced(&b) + c.mul_unreduced(&d)).montgomery_reduce()
            );
        }

        fn gen_mul(mut rng: impl RngCore) -> (Fp, FpWide<0>) {
            let (a, b) = (gen_big(&mut rng), gen_big(&mut rng));

            let ab = a * b;
            let ab_ur = a.mul_unreduced(&b);
            (ab, ab_ur)
        }

        for _ in 0..(1000 * 1000) {
            let items = [
                gen_mul(&mut rng),
                gen_mul(&mut rng),
                gen_mul(&mut rng),
                gen_mul(&mut rng),
                gen_mul(&mut rng),
                gen_mul(&mut rng),
                gen_mul(&mut rng),
                gen_mul(&mut rng),
            ];

            let total_ur = items[0].1;
            let total_ur = total_ur + items[1].1;
            let total_ur = total_ur + items[2].1;
            let total_ur = total_ur + items[3].1;
            let total_ur = total_ur + items[4].1;
            let total_ur = total_ur + items[5].1;
            let total_ur = total_ur + items[6].1;
            let total_ur = total_ur + items[7].1;

            let mut items = items.into_iter().map(|(v, _)| v);
            let total = items.next().unwrap();
            let total: Fp = items.fold(total, |total, v| total + v);
            assert_eq!(total.0, total_ur.montgomery_reduce().0);
            assert_eq!(total, total_ur.montgomery_reduce());
        }
    }
}
