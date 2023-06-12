use subtle::{Choice, ConstantTimeEq};

use crate::util::{mac, adc, carrying_add};

#[inline]
pub(super) const fn mul_wide(lhs: &[u64; 4], rhs: &[u64; 4]) -> [u64; 8] {
    // Schoolbook multiplication
    let (r0, carry) = mac(0, lhs[0], rhs[0], 0);
    let (r1, carry) = mac(0, lhs[0], rhs[1], carry);
    let (r2, carry) = mac(0, lhs[0], rhs[2], carry);
    let (r3, r4) = mac(0, lhs[0], rhs[3], carry);

    let (r1, carry) = mac(r1, lhs[1], rhs[0], 0);
    let (r2, carry) = mac(r2, lhs[1], rhs[1], carry);
    let (r3, carry) = mac(r3, lhs[1], rhs[2], carry);
    let (r4, r5) = mac(r4, lhs[1], rhs[3], carry);

    let (r2, carry) = mac(r2, lhs[2], rhs[0], 0);
    let (r3, carry) = mac(r3, lhs[2], rhs[1], carry);
    let (r4, carry) = mac(r4, lhs[2], rhs[2], carry);
    let (r5, r6) = mac(r5, lhs[2], rhs[3], carry);

    let (r3, carry) = mac(r3, lhs[3], rhs[0], 0);
    let (r4, carry) = mac(r4, lhs[3], rhs[1], carry);
    let (r5, carry) = mac(r5, lhs[3], rhs[2], carry);
    let (r6, r7) = mac(r6, lhs[3], rhs[3], carry);

    [r0, r1, r2, r3, r4, r5, r6, r7]
}

#[inline]
pub(crate) const fn square_wide(v: &[u64; 4]) -> [u64; 8] {
    let (r1, carry) = mac(0, v[0], v[1], 0);
    let (r2, carry) = mac(0, v[0], v[2], carry);
    let (r3, r4) = mac(0, v[0], v[3], carry);

    let (r3, carry) = mac(r3, v[1], v[2], 0);
    let (r4, r5) = mac(r4, v[1], v[3], carry);

    let (r5, r6) = mac(r5, v[2], v[3], 0);

    let r7 = r6 >> 63;
    let r6 = (r6 << 1) | (r5 >> 63);
    let r5 = (r5 << 1) | (r4 >> 63);
    let r4 = (r4 << 1) | (r3 >> 63);
    let r3 = (r3 << 1) | (r2 >> 63);
    let r2 = (r2 << 1) | (r1 >> 63);
    let r1 = r1 << 1;

    let (r0, carry) = mac(0, v[0], v[0], 0);
    let (r1, carry) = adc(0, r1, carry);
    let (r2, carry) = mac(r2, v[1], v[1], carry);
    let (r3, carry) = adc(0, r3, carry);
    let (r4, carry) = mac(r4, v[2], v[2], carry);
    let (r5, carry) = adc(0, r5, carry);
    let (r6, carry) = mac(r6, v[3], v[3], carry);
    let (r7, _) = adc(0, r7, carry);

    [r0, r1, r2, r3, r4, r5, r6, r7]
}


#[inline(always)]
/// The return value is bounded by $(mp^2 + Rp − p) / R$
/// where $m$ is the magnitude of the `v`, (i.e. $mp^2$ is the modulus of `v`), $R$ is $2^256$,
/// and $p$ is $52435875175126190479447740508185965837690552500527637822603658699938581184513$.
/// This means `m` must be 4 or lower, as
/// a value 88 or higher would result in overflow.
pub(super) const fn montgomery_reduce_wide(v: &[u64; 8]) -> ([u64; 4], bool) {
    use super::{MODULUS, INV};

    // The Montgomery reduction here is based on Algorithm 14.32 in
    // Handbook of Applied Cryptography
    // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.
    let [t0, t1, t2, t3, t4, t5, t6, t7] = *v;

    let k = t0.wrapping_mul(INV);
    let (_, carry) = mac(t0, k, MODULUS.0[0], 0);
    let (r1, carry) = mac(t1, k, MODULUS.0[1], carry);
    let (r2, carry) = mac(t2, k, MODULUS.0[2], carry);
    let (r3, carry) = mac(t3, k, MODULUS.0[3], carry);
    let (r4, r5) = carrying_add(t4, carry, false);

    let k = r1.wrapping_mul(INV);
    let (_, carry) = mac(r1, k, MODULUS.0[0], 0);
    let (r2, carry) = mac(r2, k, MODULUS.0[1], carry);
    let (r3, carry) = mac(r3, k, MODULUS.0[2], carry);
    let (r4, carry) = mac(r4, k, MODULUS.0[3], carry);
    let (r5, r6) = carrying_add(t5, carry, r5);

    let k = r2.wrapping_mul(INV);
    let (_, carry) = mac(r2, k, MODULUS.0[0], 0);
    let (r3, carry) = mac(r3, k, MODULUS.0[1], carry);
    let (r4, carry) = mac(r4, k, MODULUS.0[2], carry);
    let (r5, carry) = mac(r5, k, MODULUS.0[3], carry);
    let (r6, r7) = carrying_add(t6, carry, r6);

    let k = r3.wrapping_mul(INV);
    let (_, carry) = mac(r3, k, MODULUS.0[0], 0);
    let (r4, carry) = mac(r4, k, MODULUS.0[1], carry);
    let (r5, carry) = mac(r5, k, MODULUS.0[2], carry);
    let (r6, carry) = mac(r6, k, MODULUS.0[3], carry);
    let (r7, carry) = carrying_add(t7, carry, r7);

    // The caller must attempt to subtract the modulus, to ensure the value
    // is smaller than the modulus
    ([r4, r5, r6, r7], carry)
}

/// Represents an element of the scalar field $\mathbb{F}_q$ of the BLS12-381 elliptic
/// curve construction.
// The internal representation of this type is four 64-bit unsigned
// integers in little-endian order. `Scalar` values are always in
// Montgomery form; i.e., Scalar(a) = aR mod q, with R = 2^256.
#[derive(Clone, Copy, Eq)]
pub struct ScalarWide<const MAGNITUDE: usize, const VARTIME: bool = false, >(pub(crate) [u64; 8]);

impl<const MAGNITUDE: usize, const VARTIME: bool> ConstantTimeEq for ScalarWide<MAGNITUDE, VARTIME> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.0[0].ct_eq(&other.0[0])
            & self.0[1].ct_eq(&other.0[1])
            & self.0[2].ct_eq(&other.0[2])
            & self.0[3].ct_eq(&other.0[3])
            & self.0[4].ct_eq(&other.0[3])
            & self.0[5].ct_eq(&other.0[3])
            & self.0[6].ct_eq(&other.0[3])
            & self.0[7].ct_eq(&other.0[3])
    }
}

impl<const MAGNITUDE: usize, const VARTIME: bool> PartialEq for ScalarWide<MAGNITUDE, VARTIME> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        match VARTIME {
            true => self.0 == other.0,
            false => bool::from(self.ct_eq(other)),
        }
    }
}