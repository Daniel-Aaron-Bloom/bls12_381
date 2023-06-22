use core::{fmt, ops::{Add, Sub}, marker::PhantomData};

use subtle::{ConstantTimeEq, Choice};

use crate::{
    fp::{Fp, MODS},
    util::{FpWideMagnitude, adc, mac, sbb, slc, carrying_add, MulOp, SquareOp, OtherMag, borrowing_sub, Ops, FpMag, RawMagnitude, MagAdd, MagDouble, MagReduce, MagFp, MagFpWide, MagSub, MagLsh, Timing, ConstTime},
};

use super::{Mag, Never, NonZero, MontOp, DoubleOp, FpA};

#[inline(always)]
fn ct_eq(lhs: &[u64; 12], rhs: &[u64; 12]) -> Choice {
    lhs[0].ct_eq(&rhs[0])
        & lhs[1].ct_eq(&rhs[1])
        & lhs[2].ct_eq(&rhs[2])
        & lhs[3].ct_eq(&rhs[3])
        & lhs[4].ct_eq(&rhs[4])
        & lhs[5].ct_eq(&rhs[5])
        & lhs[6].ct_eq(&rhs[6])
        & lhs[7].ct_eq(&rhs[7])
        & lhs[8].ct_eq(&rhs[8])
        & lhs[9].ct_eq(&rhs[9])
        & lhs[10].ct_eq(&rhs[10])
        & lhs[11].ct_eq(&rhs[11])
}

#[inline(always)]
const fn eq_vartime(lhs: &[u64; 12], rhs: &[u64; 12]) -> bool {
    lhs[0] == rhs[0]
        && lhs[1] == rhs[1]
        && lhs[2] == rhs[2]
        && lhs[3] == rhs[3]
        && lhs[4] == rhs[4]
        && lhs[5] == rhs[5]
        && lhs[6] == rhs[6]
        && lhs[7] == rhs[7]
        && lhs[8] == rhs[8]
        && lhs[9] == rhs[9]
        && lhs[10] == rhs[10]
        && lhs[11] == rhs[11]
}

#[inline(always)]
/// The return value is bounded by $(mp^2 + Rp − p) / R$
/// where $m$ is the magnitude of the `v`, (i.e. $mp^2$ is the modulus of `v`), $R$ is $2^384$,
/// and $p$ is $4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787$.
/// This means `m` must be 87 or lower, as
/// a value 88 or higher would result in overflow.
pub(super) const fn montgomery_reduce_wide(v: &[u64; 12]) -> ([u64; 6], bool) {
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
    //let (r6, r7) = adc(t6, 0, carry);
    let (r6, r7) = carrying_add(t6, carry, false);

    let k = r1.wrapping_mul(INV);
    let (_, carry) = mac(r1, k, MODULUS[0], 0);
    let (r2, carry) = mac(r2, k, MODULUS[1], carry);
    let (r3, carry) = mac(r3, k, MODULUS[2], carry);
    let (r4, carry) = mac(r4, k, MODULUS[3], carry);
    let (r5, carry) = mac(r5, k, MODULUS[4], carry);
    let (r6, carry) = mac(r6, k, MODULUS[5], carry);
    // let (r7, r8) = adc(t7, r7, carry);
    let (r7, r8) = carrying_add(t7, carry, r7);

    let k = r2.wrapping_mul(INV);
    let (_, carry) = mac(r2, k, MODULUS[0], 0);
    let (r3, carry) = mac(r3, k, MODULUS[1], carry);
    let (r4, carry) = mac(r4, k, MODULUS[2], carry);
    let (r5, carry) = mac(r5, k, MODULUS[3], carry);
    let (r6, carry) = mac(r6, k, MODULUS[4], carry);
    let (r7, carry) = mac(r7, k, MODULUS[5], carry);
    // let (r8, r9) = adc(t8, r8, carry);
    let (r8, r9) = carrying_add(t8, carry, r8);

    let k = r3.wrapping_mul(INV);
    let (_, carry) = mac(r3, k, MODULUS[0], 0);
    let (r4, carry) = mac(r4, k, MODULUS[1], carry);
    let (r5, carry) = mac(r5, k, MODULUS[2], carry);
    let (r6, carry) = mac(r6, k, MODULUS[3], carry);
    let (r7, carry) = mac(r7, k, MODULUS[4], carry);
    let (r8, carry) = mac(r8, k, MODULUS[5], carry);
    // let (r9, r10) = adc(t9, r9, carry);
    let (r9, r10) = carrying_add(t9, carry, r9);

    let k = r4.wrapping_mul(INV);
    let (_, carry) = mac(r4, k, MODULUS[0], 0);
    let (r5, carry) = mac(r5, k, MODULUS[1], carry);
    let (r6, carry) = mac(r6, k, MODULUS[2], carry);
    let (r7, carry) = mac(r7, k, MODULUS[3], carry);
    let (r8, carry) = mac(r8, k, MODULUS[4], carry);
    let (r9, carry) = mac(r9, k, MODULUS[5], carry);
    // let (r10, r11) = adc(t10, r10, carry);
    let (r10, r11) = carrying_add(t10, carry, r10);

    let k = r5.wrapping_mul(INV);
    let (_, carry) = mac(r5, k, MODULUS[0], 0);
    let (r6, carry) = mac(r6, k, MODULUS[1], carry);
    let (r7, carry) = mac(r7, k, MODULUS[2], carry);
    let (r8, carry) = mac(r8, k, MODULUS[3], carry);
    let (r9, carry) = mac(r9, k, MODULUS[4], carry);
    let (r10, carry) = mac(r10, k, MODULUS[5], carry);
    // let (r11, carry) = adc(t11, r11, carry);
    let (r11, carry) = carrying_add(t11, carry, r11);

    // The caller must attempt to subtract the modulus, to ensure the value
    // is smaller than the modulus
    ([r6, r7, r8, r9, r10, r11], carry)
}

#[inline]
pub(super) const fn mul_wide(lhs: &[u64; 6], rhs: &[u64; 6]) -> [u64; 12] {
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
pub(crate) const fn square_wide(v: &[u64; 6]) -> [u64; 12] {
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
pub(super) const fn add_wide_c(lhs: &[u64; 12], rhs: &[u64; 12]) -> ([u64; 12], bool) {
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
    let (d11, carry) = adc(lhs[11], rhs[11], carry);

    ([d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], carry != 0)
}

#[inline]
pub(super) const fn add_wide(lhs: &[u64; 12], rhs: &[u64; 12]) -> [u64; 12] {
    let (v, _carry) = add_wide_c(lhs, rhs);

    if cfg!(debug_assertions) && _carry {
        panic!("carry != 0");
    }

    v
}

#[inline]
const fn sub_wide<const VARTIME: bool>(lhs: &[u64; 12], rhs: &[u64; 12], mut modulus: [u64; 12]) -> [u64; 12] {
    let (r0, borrow) = borrowing_sub(lhs[0], rhs[0], false);
    let (r1, borrow) = borrowing_sub(lhs[1], rhs[1], borrow);
    let (r2, borrow) = borrowing_sub(lhs[2], rhs[2], borrow);
    let (r3, borrow) = borrowing_sub(lhs[3], rhs[3], borrow);
    let (r4, borrow) = borrowing_sub(lhs[4], rhs[4], borrow);
    let (r5, borrow) = borrowing_sub(lhs[5], rhs[5], borrow);
    let (r6, borrow) = borrowing_sub(lhs[6], rhs[6], borrow);
    let (r7, borrow) = borrowing_sub(lhs[7], rhs[7], borrow);
    let (r8, borrow) = borrowing_sub(lhs[8], rhs[8], borrow);
    let (r9, borrow) = borrowing_sub(lhs[9], rhs[9], borrow);
    let (r10, borrow) = borrowing_sub(lhs[10], rhs[10], borrow);
    let (r11, borrow) = borrowing_sub(lhs[11], rhs[11], borrow);

    let v = [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11];
    match VARTIME {
        true if borrow => add_wide_c(&v, &modulus).0,
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
            modulus[6] &= borrow;
            modulus[7] &= borrow;
            modulus[8] &= borrow;
            modulus[9] &= borrow;
            modulus[10] &= borrow;
            modulus[11] &= borrow;
            add_wide_c(&v, &modulus).0
        }
    }
}

#[inline]
const fn sub_widet<T: Timing>(lhs: &[u64; 12], rhs: &[u64; 12], mut modulus: [u64; 12]) -> [u64; 12] {
    let (r0, borrow) = borrowing_sub(lhs[0], rhs[0], false);
    let (r1, borrow) = borrowing_sub(lhs[1], rhs[1], borrow);
    let (r2, borrow) = borrowing_sub(lhs[2], rhs[2], borrow);
    let (r3, borrow) = borrowing_sub(lhs[3], rhs[3], borrow);
    let (r4, borrow) = borrowing_sub(lhs[4], rhs[4], borrow);
    let (r5, borrow) = borrowing_sub(lhs[5], rhs[5], borrow);
    let (r6, borrow) = borrowing_sub(lhs[6], rhs[6], borrow);
    let (r7, borrow) = borrowing_sub(lhs[7], rhs[7], borrow);
    let (r8, borrow) = borrowing_sub(lhs[8], rhs[8], borrow);
    let (r9, borrow) = borrowing_sub(lhs[9], rhs[9], borrow);
    let (r10, borrow) = borrowing_sub(lhs[10], rhs[10], borrow);
    let (r11, borrow) = borrowing_sub(lhs[11], rhs[11], borrow);

    let v = [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11];
    match T::VAR {
        true if borrow => add_wide_c(&v, &modulus).0,
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
            modulus[6] &= borrow;
            modulus[7] &= borrow;
            modulus[8] &= borrow;
            modulus[9] &= borrow;
            modulus[10] &= borrow;
            modulus[11] &= borrow;
            add_wide_c(&v, &modulus).0
        }
    }
}

#[inline]
pub const fn double_wide_c(v: &[u64; 12], pow: u32) -> ([u64; 12], bool) {
    let (d0, carry) = slc(v[0], pow, 0);
    let (d1, carry) = slc(v[1], pow, carry);
    let (d2, carry) = slc(v[2], pow, carry);
    let (d3, carry) = slc(v[3], pow, carry);
    let (d4, carry) = slc(v[4], pow, carry);
    let (d5, carry) = slc(v[5], pow, carry);
    let (d6, carry) = slc(v[6], pow, carry);
    let (d7, carry) = slc(v[7], pow, carry);
    let (d8, carry) = slc(v[8], pow, carry);
    let (d9, carry) = slc(v[9], pow, carry);
    let (d10, carry) = slc(v[10], pow, carry);
    let (d11, carry) = slc(v[11], pow, carry);

    ([d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], carry != 0)
}

#[inline]
pub const fn double_wide(v: &[u64; 12], pow: u32) -> [u64; 12] {
    let (v, _carry) = double_wide_c(v, pow);

    if cfg!(debug_assertions) && _carry {
        panic!("carry != 0");
    }

    v
}

/// Negates an element by subtracting it from the `Self::MODULUS`
#[inline]
const fn negate_wide(v: &[u64; 12], modulus: &[u64; 12]) -> [u64; 12] {
    let (d0, borrow) = borrowing_sub(modulus[0], v[0], false);
    let (d1, borrow) = borrowing_sub(modulus[1], v[1], borrow);
    let (d2, borrow) = borrowing_sub(modulus[2], v[2], borrow);
    let (d3, borrow) = borrowing_sub(modulus[3], v[3], borrow);
    let (d4, borrow) = borrowing_sub(modulus[4], v[4], borrow);
    let (d5, borrow) = borrowing_sub(modulus[5], v[5], borrow);
    let (d6, borrow) = borrowing_sub(modulus[6], v[6], borrow);
    let (d7, borrow) = borrowing_sub(modulus[7], v[7], borrow);
    let (d8, borrow) = borrowing_sub(modulus[8], v[8], borrow);
    let (d9, borrow) = borrowing_sub(modulus[9], v[9], borrow);
    let (d10, borrow) = borrowing_sub(modulus[10], v[10], borrow);
    let (d11, _borrow) = borrowing_sub(modulus[11], v[11], borrow);

    if cfg!(debug_assertions) && _borrow {
        panic!("borrow != 0");
    }

    [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]
}

#[inline]
pub const fn subtract_p_wide<const VARTIME: bool>(msb: bool, v: &[u64; 12], modulus: &[u64; 12]) -> [u64; 12] {
    let (r0, borrow) = borrowing_sub(v[0], modulus[0], false);
    let (r1, borrow) = borrowing_sub(v[1], modulus[1], borrow);
    let (r2, borrow) = borrowing_sub(v[2], modulus[2], borrow);
    let (r3, borrow) = borrowing_sub(v[3], modulus[3], borrow);
    let (r4, borrow) = borrowing_sub(v[4], modulus[4], borrow);
    let (r5, borrow) = borrowing_sub(v[5], modulus[5], borrow);
    let (r6, borrow) = borrowing_sub(v[6], modulus[6], borrow);
    let (r7, borrow) = borrowing_sub(v[7], modulus[7], borrow);
    let (r8, borrow) = borrowing_sub(v[8], modulus[8], borrow);
    let (r9, borrow) = borrowing_sub(v[9], modulus[9], borrow);
    let (r10, borrow) = borrowing_sub(v[10], modulus[10], borrow);
    let (r11, borrow) = borrowing_sub(v[11], modulus[11], borrow);

    match VARTIME {
        true if borrow > msb => *v,
        true => [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11],
        false => {
            // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
            // borrow = 0x000...000. Thus, we use it as a mask!
            let borrow = -(borrow as i64) as u64;
            [
                (v[0] & borrow) | (r0 & !borrow),
                (v[1] & borrow) | (r1 & !borrow),
                (v[2] & borrow) | (r2 & !borrow),
                (v[3] & borrow) | (r3 & !borrow),
                (v[4] & borrow) | (r4 & !borrow),
                (v[5] & borrow) | (r5 & !borrow),
                (v[6] & borrow) | (r6 & !borrow),
                (v[7] & borrow) | (r7 & !borrow),
                (v[8] & borrow) | (r8 & !borrow),
                (v[9] & borrow) | (r9 & !borrow),
                (v[10] & borrow) | (r10 & !borrow),
                (v[11] & borrow) | (r11 & !borrow),
            ]
        }
    }
}
#[inline]
pub const fn subtract_p_widet<T: Timing>(msb: bool, v: &[u64; 12], modulus: &[u64; 12]) -> [u64; 12] {
    let (r0, borrow) = borrowing_sub(v[0], modulus[0], false);
    let (r1, borrow) = borrowing_sub(v[1], modulus[1], borrow);
    let (r2, borrow) = borrowing_sub(v[2], modulus[2], borrow);
    let (r3, borrow) = borrowing_sub(v[3], modulus[3], borrow);
    let (r4, borrow) = borrowing_sub(v[4], modulus[4], borrow);
    let (r5, borrow) = borrowing_sub(v[5], modulus[5], borrow);
    let (r6, borrow) = borrowing_sub(v[6], modulus[6], borrow);
    let (r7, borrow) = borrowing_sub(v[7], modulus[7], borrow);
    let (r8, borrow) = borrowing_sub(v[8], modulus[8], borrow);
    let (r9, borrow) = borrowing_sub(v[9], modulus[9], borrow);
    let (r10, borrow) = borrowing_sub(v[10], modulus[10], borrow);
    let (r11, borrow) = borrowing_sub(v[11], modulus[11], borrow);

    match T::VAR {
        true if borrow > msb => *v,
        true => [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11],
        false => {
            // If underflow occurred on the final limb, borrow = 0xfff...fff, otherwise
            // borrow = 0x000...000. Thus, we use it as a mask!
            let borrow = -(borrow as i64) as u64;
            [
                (v[0] & borrow) | (r0 & !borrow),
                (v[1] & borrow) | (r1 & !borrow),
                (v[2] & borrow) | (r2 & !borrow),
                (v[3] & borrow) | (r3 & !borrow),
                (v[4] & borrow) | (r4 & !borrow),
                (v[5] & borrow) | (r5 & !borrow),
                (v[6] & borrow) | (r6 & !borrow),
                (v[7] & borrow) | (r7 & !borrow),
                (v[8] & borrow) | (r8 & !borrow),
                (v[9] & borrow) | (r9 & !borrow),
                (v[10] & borrow) | (r10 & !borrow),
                (v[11] & borrow) | (r11 & !borrow),
            ]
        }
    }
}

pub const fn reduce_full_wide<const VARTIME: bool>(mut imag: usize, omag: usize, mut v: [u64; 12], mut msb: bool, ) -> [u64; 12] {
    while imag > omag {
        v = subtract_p_wide::<VARTIME>(msb, &v, &WIDE_MODS[(imag-1) / 2]);
        msb = false;
        imag = imag / 2;
    }
    return v
}
pub const fn reduce_full_widet<T: Timing>(mut imag: usize, omag: usize, mut v: [u64; 12], mut msb: bool, ) -> [u64; 12] {
    while imag > omag {
        v = subtract_p_widet::<T>(msb, &v, &WIDE_MODS[(imag-1) / 2]);
        msb = false;
        imag = imag / 2;
    }
    return v
}

/// The unreduced result of `Fp` multiplication.
/// The internal representation of this type is twelve 64-bit unsigned
/// integers in little-endian order. `FpWide` values are always in
/// double Montgomery form; i.e., FpWide<M>(a) = a*R^2 mod M*p^2, with R = 2^384.
/// MAGNITUDE must be 95 or less to prevent overflow
#[derive(Debug, Clone, Copy)]
pub struct FpWide<const MAGNITUDE: usize, const VARTIME: bool = false>([u64; 12]);

/// The unreduced result of `Fp` multiplication.
/// The internal representation of this type is twelve 64-bit unsigned
/// integers in little-endian order. `FpWide` values are always in
/// double Montgomery form; i.e., FpWide<M>(a) = a*R^2 mod M*p^2, with R = 2^384.
/// MAGNITUDE must be 95 or less to prevent overflow
#[derive(Clone, Copy)]
pub struct FpAWide<Mag: FpWideMagnitude = FpMag<0>, T: Timing = ConstTime>([u64; 12], PhantomData<(Mag, T)>);

impl<Mag: FpWideMagnitude, T: Timing> fmt::Debug for FpAWide<Mag, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "0x")?;
        for &b in self.0.iter() {
            write!(f, "{:02x}", b)?;
        }
        Ok(())
    }
}


impl<Mag: FpWideMagnitude, T: Timing> ConstantTimeEq for FpAWide<Mag, T> {
    fn ct_eq(&self, other: &Self) -> Choice {
        ct_eq(&self.0, &other.0)
    }
}

impl<Mag: FpWideMagnitude, T: Timing> Eq for FpAWide<Mag, T> {}
impl<Mag: FpWideMagnitude, T: Timing> PartialEq for FpAWide<Mag, T> {
    fn eq(&self, other: &Self) -> bool {
        match T::VAR {
            true => self.0 == other.0,
            false => bool::from(self.ct_eq(other)),
        }
    }
}


impl<const MAGNITUDE: usize, const VARTIME: bool> OtherMag for FpWide<MAGNITUDE, VARTIME> {
    const MAGNITUDE: usize = MAGNITUDE;
    type Mag<const MAG2: usize> = FpWide<MAG2, VARTIME>;
}

// MAGNITUDE cannot be above 95, or else
impl<const MAGNITUDE: usize, const VARTIME: bool> FpWide<MAGNITUDE, VARTIME> {
    #[inline(always)]
    pub const fn vartime<const VARTIME2: bool>(self) -> FpWide<MAGNITUDE, VARTIME2> {
        FpWide(self.0)
    }
}

pub type FpWideReduce<Mag> = MagFp<MagReduce<Mag>>;
pub type FpWideAdd<Lhs, Rhs> = MagFpWide<MagAdd<Lhs, Rhs>>;
pub type FpWideDouble<Mag> = MagFpWide<MagDouble<Mag>>;
pub type FpWideLsh<Mag, const P: usize> = MagFpWide<MagLsh<Mag, P>>;
pub type FpWideSub<Lhs, Rhs> = MagFpWide<MagSub<Lhs, Rhs>>;

impl<Mag: FpWideMagnitude, T: Timing> FpAWide<Mag, T> {
    /// Constructs an element of `FpWide` without checking that it is
    /// canonical.
    #[inline(always)]
    pub const fn from_raw_unchecked(v: [u64; 12]) -> Self {
        Self(v, PhantomData)
    }

    /// Returns zero, the additive identity.
    #[inline(always)]
    pub const fn zero() -> Self {
        Self::from_raw_unchecked([0; 12])
    }

    #[inline(always)]
    pub const fn vartime<T2: Timing>(self) -> FpAWide<Mag, T2> {
        FpAWide::from_raw_unchecked(self.0)
    }

    #[inline]
    pub const fn mag<MagR: FpWideMagnitude>(self) -> FpAWide<MagR, T> {
        FpAWide::from_raw_unchecked(reduce_full_widet::<T>(Mag::MAG, MagR::MAG, self.0, false))
    }

    #[inline(always)]
    pub fn eq<RMag: FpWideMagnitude>(&self, rhs: &FpAWide<RMag, T>) -> Choice {
        self.sub(rhs).is_zero()
    }

    #[inline(always)]
    pub const fn eq_vartime<RMag: FpWideMagnitude>(&self, rhs: &FpAWide<RMag, T>) -> bool {
        self.sub(rhs).is_zero_vartime()
    }

    #[inline]
    pub fn is_zero(&self) -> Choice {
        self.montgomery_reduce().is_zero()
    }

    #[inline]
    pub const fn is_zero_vartime(&self) -> bool {
        self.montgomery_reduce().is_zero_vartime()
    }

    #[inline(always)]
    pub const fn montgomery_reduce(self) -> FpA<FpWideReduce<Mag>, T> {
        let (v, msb) = montgomery_reduce_wide(&self.0);
        let v = super::reduce_full_const::<MagReduce<Mag>, FpWideReduce<Mag>, T>(v, msb);
        FpA::from_raw_unchecked(v)
    }

    #[inline(always)]
    pub const fn add<RMag: FpWideMagnitude>(&self, rhs: &FpAWide<RMag, T>) -> FpAWide<FpWideAdd<Mag, RMag>, T> {
        let (v, msb) = add_wide_c(&self.0, &rhs.0);
        let v = reduce_full_widet::<T>(MagAdd::<Mag, RMag>::MAG, FpWideAdd::<Mag, RMag>::MAG, v, msb);
        FpAWide::from_raw_unchecked(v)
    }

    #[inline(always)]
    pub const fn double(&self) -> FpAWide<FpWideDouble<Mag>, T> {
        let (v, msb) = double_wide_c(&self.0, 1);
        let v = reduce_full_widet::<T>(MagDouble::<Mag>::MAG, FpWideDouble::<Mag>::MAG, v, msb);
        FpAWide::from_raw_unchecked(v)
    }

    #[inline(always)]
    pub const fn lsh<const P: usize>(&self) -> FpAWide<MagFpWide<Mag>, T>
    where FpMag<P>: RawMagnitude {
        let (v, msb) = double_wide_c(&self.0, P as u32);
        let v = reduce_full_widet::<T>(MagLsh::<Mag, P>::MAG, MagFpWide::<Mag>::MAG, v, msb);
        FpAWide::from_raw_unchecked(v)
    }

    #[inline(always)]
    pub const fn sub<RMag: FpWideMagnitude>(&self, rhs: &FpAWide<RMag, T>) -> FpAWide<FpWideSub<Mag, RMag>, T> {
        let v = sub_widet::<T>(&self.0, &rhs.0, WIDE_MODS[FpWideSub::<Mag, RMag>::MAG]);
        FpAWide::from_raw_unchecked(v)
    }
}


#[inline(always)]
pub const fn montgomery_reduce<const MAGNITUDE: usize, const VARTIME: bool>(v: &[u64; 12]) -> [u64; 6] {
    use super::{subtract_p, P5};
    let (mut v, msb) = montgomery_reduce_wide(v);

    if MAGNITUDE >= 87 {
        // 86 indicates a mod of $87p^2$
        // When you plug 87 into `montgomery_reduce_wide` for $m$
        // you get an output bound of just under $2^384$
        // 87 indicates a mod of $88p^2$
        // When you plug 88 into `montgomery_reduce_wide` for $m$
        // you get an output bound of just over $2^384$
        // So anything value which is mod $88p^2$ and above might overflow,
        // We reduce that by 5p so it fits more neatly, but account for msb
        v = subtract_p::<VARTIME>(msb, &v, &P5)
    } else if MAGNITUDE >= 78 {
        // 78 indicates a mod of 79p^2
        // When you plug 79 into `montgomery_reduce_wide` for $m$
        // you get an output bound of just over $9p$
        // We reduce that by 5p so it fits more neatly
        v = subtract_p::<VARTIME>(false, &v, &P5)
    }
    v
}

#[inline(always)]
pub const fn montgomery_reduce_full<const VARTIME: bool>(imag: usize, omag: usize, v: &[u64; 12]) -> [u64; 6] {
    use super::subtract_p;
    let (mut v, msb) = montgomery_reduce_wide(&v);
    let imag = match () {
        () if imag <= 8 => 1,
        () if imag <= 18 => 2,
        () if imag <= 28 => 3,
        () if imag <= 38 => 4,
        () if imag <= 48 => 5,
        () if imag <= 58 => 6,
        () if imag <= 67 => 7,
        () if imag <= 77 => 8,
        () if imag <= 87 => {
            v = subtract_p::<VARTIME>(false, &v, &MODS[4]);
            4
        },
        () => {
            v = subtract_p::<VARTIME>(msb, &v, &MODS[4]);
            5
        },
    };

    super::reduce_full::<VARTIME>(imag, omag, v, false)
}

macro_rules! montgomery_reduce {
    ($($(($($ua:literal),+) => $ub:literal),+ $(,)?)?) => {$($($(
impl<const VARTIME: bool> MontOp for FpWide<$ua, VARTIME> {
    type MontOut = Fp<$ub, VARTIME>;
    #[inline(always)]
    fn montgomery_reduce(lhs: &Self) -> Self::MontOut {
        Fp(montgomery_reduce::<$ua, VARTIME>(&lhs.0))
    }
}
impl<const VARTIME: bool> FpWide<$ua, VARTIME> {
    #[inline(always)]
    pub const fn montgomery_reduce(&self) -> Fp<$ub, VARTIME> {
        Fp(montgomery_reduce::<$ua, VARTIME>(&self.0))
    }
}
    )+)+)?};
}

montgomery_reduce!{
    // 0 indicates a mod of 1p^2
    // When you plug 1 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just over $1p$ (indicated by `=> 1`)
    //
    // 8 indicates a mod of 9p^2
    // When you plug 9 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just under $2p$ (indicated by `=> 1`)
    (0, 1, 2, 3, 4, 5, 6, 7, 8) => 1,

    // 9 indicates a mod of 10p^2
    // When you plug 10 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just over $2p$ (indicated by `=> 2`)
    //
    // 28 indicates a mod of 29p^2
    // When you plug 29 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just under $3p$ (indicated by `=> 2`)
    (9, 10, 11, 12, 13, 14, 15, 16, 17, 18) => 2,

    // 19 indicates a mod of 20p^2
    // When you plug 10 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just over $3p$ (indicated by `=> 3`)
    //
    // 28 indicates a mod of 29p^2
    // When you plug 29 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just under $4p$ (indicated by `=> 3`)
    (19, 20, 21, 22, 23, 24, 25, 26, 27, 28) => 3,

    // 29 indicates a mod of 30p^2
    // When you plug 30 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just over $4p$ (indicated by `=> 4`)
    //
    // 38 indicates a mod of 39p^2
    // When you plug 39 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just under $5p$ (indicated by `=> 4`)
    (29, 30, 31, 32, 33, 34, 35, 36, 37, 38) => 4,

    // 39 indicates a mod of 40p^2
    // When you plug 40 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just over $5p$ (indicated by `=> 5`)
    //
    // 48 indicates a mod of 49p^2
    // When you plug 49 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just under $6p$ (indicated by `=> 5`)
    (39, 40, 41, 42, 43, 44, 45, 46, 47, 48) => 5,

    // 49 indicates a mod of 50p^2
    // When you plug 50 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just over $6p$ (indicated by `=> 6`)
    //
    // 58 indicates a mod of 59p^2
    // When you plug 59 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just under $7p$ (indicated by `=> 6`)
    (49, 50, 51, 52, 53, 54, 55, 56, 57, 58) => 6,

    // 59 indicates a mod of 60p^2
    // When you plug 60 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just over $7p$ (indicated by `=> 7`)
    //
    // 67 indicates a mod of 68p^2
    // When you plug 68 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just under $8p$ (indicated by `=> 7`)
    (59, 60, 61, 62, 63, 64, 65, 66, 67) => 7,

    // 68 indicates a mod of 69p^2
    // When you plug 69 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just over $8p$ (indicated by `=> 8`)
    //
    // 77 indicates a mod of 78p^2
    // When you plug 78 into `montgomery_reduce_wide` for $m$
    // you get an output bound of just under $9p$ (indicated by `=> 8`)
    (68, 69, 70, 71, 72, 73, 74, 75, 76, 77) => 8,

    // Values over 9p are in a weird situation because 10p cannot be stored
    // properly in 384 bits. As such they get reduced by 5p by `montgomery_reduce`.
    (78, 79, 80, 81, 82, 83, 84, 85, 86, 87) => 4,
    (88, 89, 90, 91, 92, 93, 94, 95) => 5,
}

// MAGNITUDE cannot be above 87, or else
impl<const MAGNITUDE: usize, const VARTIME: bool> FpWide<MAGNITUDE, VARTIME> {
    #[inline(always)]
    pub const fn montgomery_reduce_full(self) -> Fp<0, VARTIME> {
        use super::subtract_p;
        let (mut v, msb) = montgomery_reduce_wide(&self.0);

        if MAGNITUDE >= 87 {
            v = subtract_p::<VARTIME>(msb, &v, &MODS[7]);
        } else if MAGNITUDE >= 68 {
            v = subtract_p::<VARTIME>(false, &v, &MODS[7]);
        }

        if MAGNITUDE >= 29 {
            v = subtract_p::<VARTIME>(false, &v, &MODS[3]);
        }

        if MAGNITUDE >= 9 {
            v = subtract_p::<VARTIME>(false, &v, &MODS[1]);
        }

        Fp(subtract_p::<VARTIME>(false, &v, &MODS[0]))
    }
}
macro_rules! mul_helper {
    ($ua:literal {$($ub:literal)*}) => {$(
impl<const VARTIME: bool> MulOp<$ub> for Fp<$ua, VARTIME> {
    type MulOut = FpWide<{($ua+1)*($ub+1)-1}, VARTIME>;
    fn mul(lhs: &Self, rhs: &Self::Mag<$ub>) -> Self::MulOut {
        FpWide(mul_wide(&lhs.0, &rhs.0))
    }
})*
impl<const VARTIME: bool> SquareOp for Fp<$ua, VARTIME> {
    type SquareOut = FpWide<{($ua+1)*($ua+1)-1}, VARTIME>;
    fn square(lhs: &Self) -> Self::SquareOut {
        FpWide(square_wide(&lhs.0))
    }
}
impl<const VARTIME: bool> Fp<$ua, VARTIME> {
    pub const fn square_wide(&self) -> FpWide<{($ua+1)*($ua+1)-1}, VARTIME> {
        FpWide(square_wide(&self.0))
    }
}
    };
    ({$($ua:literal)*} $ub:tt) => {$(
        mul_helper!{$ua $ub}
    )*};
}

macro_rules! mul_impl {
    ($($($ua:literal),+ $(,)?)?) => {
        mul_helper!{{$($($ua)+)?} {$($($ua)+)?}}
    };
}

mul_impl!{0,1,2,3,4,5,6,7,8}

macro_rules! impl_double {
    ($pow:literal: $($($ua:literal),+ $(,)?)?) => {$($(
impl<const VARTIME: bool> DoubleOp<$pow> for FpWide<$ua, VARTIME> {
    type DoubleOut = FpWide<{($ua+1)*(1<<($pow+1))-1}, VARTIME>;
    fn double(lhs: &Self) -> Self::DoubleOut {
        FpWide(double_wide(&lhs.0, $pow+1))
    }
}
    )+)?};
}

impl_double!{
    0: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
    10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
    30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
    40, 41, 42, 43, 44, 45, 46, 47
}
impl_double!{
    1: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
    10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23
}
impl_double!{
    2: 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
    10, 11
}
impl_double!{3: 0, 1, 2, 3, 4, 5}
impl_double!{4: 0, 1, 2}
impl_double!{5: 0}

impl<const VARTIME: bool> FpWide<0, VARTIME> {
    #[inline(always)]
    pub const fn from_mul(lhs: &Fp<0, VARTIME>, rhs: &Fp<0, VARTIME>) -> Self {
        Self(mul_wide(&lhs.0, &rhs.0))
    }

    #[inline(always)]
    pub const fn from_square(v: &Fp<0, VARTIME>) -> Self {
        Self(square_wide(&v.0))
    }
}


const MODULUS_INCREMENT: [u64; 12] = square_wide(&super::MODULUS);

macro_rules! wide_impl {
    ($($($ua:literal),+ $(,)?)?) => {$($(
impl<const VARTIME: bool> Mag<1, [u64; 12]> for FpWide<$ua, VARTIME> {
    type Prev = FpWide<{$ua - 1}, VARTIME>;
    type Next = FpWide<{$ua + 1}, VARTIME>;

    /// A multiple of the prime that is larger than this element could be (p^2).
    const MODULUS: [u64; 12] = add_wide(&Self::Prev::MODULUS, &MODULUS_INCREMENT);

    #[inline(always)]
    fn make([v]: [[u64; 12]; 1]) -> Self {
        Self(v)
    }
    #[inline(always)]
    fn data(&self) -> [&[u64; 12]; 1] {
        [&self.0]
    }
    #[inline(always)]
    fn negate(&self) -> Self {
        Self::make([negate_wide(self.data()[0], &Self::MODULUS)])
    }
}

impl<const VARTIME: bool> NonZero for FpWide<$ua, VARTIME> {}
    )+)?};
}

impl<const VARTIME: bool> Mag<1, [u64; 12]> for FpWide<0, VARTIME> {
    type Prev = Never;
    type Next = FpWide<1, VARTIME>;

    /// A multiple of the prime that is larger than this element could be (p^2).
    const MODULUS: [u64; 12] = MODULUS_INCREMENT;

    #[inline(always)]
    fn make([v]: [[u64; 12]; 1]) -> Self {
        Self(v)
    }
    #[inline(always)]
    fn data(&self) -> [&[u64; 12]; 1] {
        [&self.0]
    }
    #[inline(always)]
    fn negate(&self) -> Self {
        Self::make([negate_wide(self.data()[0], &Self::MODULUS)])
    }
}

wide_impl! {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94}
impl<const VARTIME: bool> Mag<1, [u64; 12]> for FpWide<95, VARTIME> {
    type Prev = FpWide<94, VARTIME>;
    type Next = Never;

    /// A multiple of the prime that is larger than this element could be (p^2).
    const MODULUS: [u64; 12] = add_wide(&Self::Prev::MODULUS, &MODULUS_INCREMENT);

    #[inline(always)]
    fn make([v]: [[u64; 12]; 1]) -> Self {
        Self(v)
    }
    #[inline(always)]
    fn data(&self) -> [&[u64; 12]; 1] {
        [&self.0]
    }
    #[inline(always)]
    fn negate(&self) -> Self {
        Self::make([negate_wide(self.data()[0], &Self::MODULUS)])
    }
}

impl<const MAG2: usize, const VARTIME: bool> Ops<1, [u64; 12], FpWide<MAG2, VARTIME>> for FpWide<0, VARTIME>
where
    FpWide<MAG2, VARTIME>: Mag<1, [u64; 12]>,
{
    type OpOut = <FpWide<MAG2, VARTIME> as Mag<1, [u64; 12]>>::Next;
    #[inline(always)]
    fn add(lhs: &Self, rhs: &FpWide<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([add_wide(&lhs.0, &rhs.0)])
    }
    #[inline(always)]
    fn sub(lhs: &Self, rhs: &FpWide<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([sub_wide::<VARTIME>(&lhs.0, &rhs.0, <Self::OpOut>::MODULUS)])
    }
}

impl<const MAG1: usize, const MAG2: usize, const VARTIME: bool> Ops<1, [u64; 12], FpWide<MAG2, VARTIME>> for FpWide<MAG1, VARTIME>
where
    FpWide<MAG1, VARTIME>: Mag<1, [u64; 12]> + NonZero,
    <FpWide<MAG1, VARTIME> as Mag<1, [u64; 12]>>::Prev: Ops<1, [u64; 12], FpWide<MAG2, VARTIME>>,
    FpWide<MAG2, VARTIME>: Mag<1, [u64; 12]>,
{
    type OpOut = <<<FpWide<MAG1, VARTIME> as Mag<1, [u64; 12]>>::Prev as Ops<1, [u64; 12], FpWide<MAG2, VARTIME>>>::OpOut as Mag<
        1,
        [u64; 12],
    >>::Next;
    #[inline(always)]
    fn add(lhs: &Self, rhs: &FpWide<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([add_wide(lhs.data()[0], rhs.data()[0])])
    }
    #[inline(always)]
    fn sub(lhs: &Self, rhs: &FpWide<MAG2, VARTIME>) -> Self::OpOut {
        Mag::make([sub_wide::<VARTIME>(&lhs.0, &rhs.0, <Self::OpOut>::MODULUS)])
    }
}

impl<'a, 'b, const MAG1: usize, const MAG2: usize, const VARTIME: bool> Add<&'b FpWide<MAG2, VARTIME>> for &'a FpWide<MAG1, VARTIME>
where
    FpWide<MAG1, VARTIME>: Ops<1, [u64; 12], FpWide<MAG2, VARTIME>>,
    <FpWide<MAG1, VARTIME> as OtherMag>::Mag<MAG2>: Mag<1, [u64; 12]>,
    for<'j> &'j FpWide<MAG2, VARTIME>: Into<&'j <FpWide<MAG1, VARTIME> as OtherMag>::Mag<MAG2>>,
{
    type Output = <FpWide<MAG1, VARTIME> as Ops<1, [u64; 12], FpWide<MAG2, VARTIME>>>::OpOut;

    #[inline(always)]
    fn add(self, rhs: &'b FpWide<MAG2, VARTIME>) -> Self::Output {
        Ops::add(self, rhs.into())
    }
}
impl<'a, 'b, const MAG1: usize, const MAG2: usize, const VARTIME: bool> Sub<&'b FpWide<MAG2, VARTIME>> for &'a FpWide<MAG1, VARTIME>
where
    FpWide<MAG1, VARTIME>: Ops<1, [u64; 12], FpWide<MAG2, VARTIME>>,
    <FpWide<MAG1, VARTIME> as OtherMag>::Mag<MAG2>: Mag<1, [u64; 12]>,
    for<'j> &'j FpWide<MAG2, VARTIME>: Into<&'j <FpWide<MAG1, VARTIME> as OtherMag>::Mag<MAG2>>,
{
    type Output = <FpWide<MAG1, VARTIME> as Ops<1, [u64; 12], FpWide<MAG2, VARTIME>>>::OpOut;

    #[inline(always)]
    fn sub(self, rhs: &'b FpWide<MAG2, VARTIME>) -> Self::Output {
        Ops::sub(self, rhs.into())
    }
}

impl_binops_additive_output! {
{const MAG1: usize, const MAG2: usize, const VARTIME: bool}
{where FpWide<MAG1, VARTIME>: Ops<1, [u64; 12], FpWide<MAG2, VARTIME>>, <FpWide<MAG1, VARTIME> as OtherMag>::Mag<MAG2>: Mag<1, [u64; 12]>, for<'j> &'j FpWide<MAG2, VARTIME>: Into<&'j <FpWide<MAG1, VARTIME> as OtherMag>::Mag<MAG2>>}
{FpWide<MAG1, VARTIME>}
{FpWide<MAG2, VARTIME>}}

macro_rules! wide_double_impl {
($($($ua:literal),+ $(,)?)?) => {$($(
impl<const VARTIME: bool> FpWide<$ua, VARTIME> {
    #[inline(always)]
    pub const fn double(&self) -> FpWide<{$ua*2 + 1}, VARTIME> {
        FpWide(double_wide(&self.0, 1))
    }
}
)+)?};
}

wide_double_impl! {
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42
}

macro_rules! mods {
    ($i:ident: $t:ty = $($m:literal)+) => {
pub const $i: [$t; {$(({let _ = $m; 1}) + )+ 0}] = [$(
    <FpWide<$m, false> as Mag<1, _>>::MODULUS,
)+];
    };
}

mods!{WIDE_MODS: [u64; 12] = 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90 91 92 93 94 95}

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
    fn test_sub() {
        use rand_core::SeedableRng;
        let mut rng = rand_xorshift::XorShiftRng::from_seed([
            0x57, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06,
            0xbc, 0xe5,
        ]);
        for _ in 0..1_000_000 {
            let a = gen_big(&mut rng);
            let b = gen_big(&mut rng);
            let c = gen_big(&mut rng);
            let d = gen_big(&mut rng);
            let a_ur = a.mul_unreduced(&b);
            let b_ur = c.mul_unreduced(&d);

            let _ = a_ur - b_ur;
        }
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
            assert_eq!(v_5.0, v_5_ur.montgomery_reduce_full().0);

            let v_10 = v_5.double();
            let v_10_ur = v_5_ur + v_5_ur;
            assert_eq!(v_10.0, v_10_ur.montgomery_reduce_full().0, "{}", i);

            let v = v.double() + v;
            let v_ur = v_ur.double() + v_ur;
            assert_eq!(v.0, v_ur.montgomery_reduce_full().0);

            let v = v.double();
            let v_ur = v_ur.double();
            assert_eq!(v.0, v_ur.montgomery_reduce_full().0);

            let v = v.double();
            let v_ur = v_ur.double();
            assert_eq!(v.0, v_ur.montgomery_reduce_full().0);

            let v = v.double();
            let v_ur = v_ur.double();
            assert_eq!(v.0, v_ur.montgomery_reduce_full().0);

            let v = v.double();
            let v_ur = v_ur.double();
            assert_eq!(v.0, v_ur.montgomery_reduce_full().0);

            let v = v_10.double().double();
            let v_ur = v_10_ur.double().double();
            assert_eq!(v.0, v_ur.montgomery_reduce_full().0);

            let v = v.double() + v_5;
            let v_ur: FpWide<84> = v_ur.double() + v_5_ur;
            assert_eq!(v, v_ur.montgomery_reduce_full(), "{}", i);
            assert_eq!(v.0, v_ur.montgomery_reduce_full().0, "{}", i);
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

            assert_eq!(double_wide(&v.0, 1), add_wide(&v.0, &v.0))
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
            let [a, b, c, d] = [(); 4].map(|_| Fp::<0, false>::random(&mut rng));

            assert_eq!(
                a * b + c * d,
                (a.mul_unreduced(&b) + c.mul_unreduced(&d)).montgomery_reduce_full()
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
            assert_eq!(total.0, total_ur.montgomery_reduce_full().0);
            assert_eq!(total, total_ur.montgomery_reduce_full());
        }
    }
}
