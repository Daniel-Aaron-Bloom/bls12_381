#![allow(missing_docs)]
use core::fmt;
use subtle::Choice;

/// Compute a + b + carry, returning the result and the new carry over.
#[inline(always)]
pub const fn adc(a: u64, b: u64, carry: u64) -> (u64, u64) {
    let ret = (a as u128) + (b as u128) + (carry as u128);
    (ret as u64, (ret >> 64) as u64)
}

/// Compute a - (b + borrow), returning the result and the new borrow.
#[inline(always)]
pub const fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let ret = (a as u128).wrapping_sub((b as u128) + ((borrow >> 63) as u128));
    (ret as u64, (ret >> 64) as u64)
}

/// Calculates `lhs + rhs + carry` without the ability to overflow.
///
/// Performs "signed ternary addition" which takes in an extra bit to add, and may return an
/// additional bit of overflow. This signed function is used only on the highest-ordered data,
/// for which the signed overflow result indicates whether the big integer overflowed or not.
#[inline(always)]
pub const fn carrying_add(lhs: u64, rhs: u64, carry: bool) -> (u64, bool) {
    // note: longer-term this should be done via an intrinsic.
    // note: no intermediate overflow is required (https://github.com/rust-lang/rust/issues/85532#issuecomment-1032214946).
    let (a, b) = lhs.overflowing_add(rhs);
    let (c, d) = a.overflowing_add(carry as u64);
    (c, b != d)
}

/// Calculates `lhs - rhs - borrow` without the ability to overflow.
///
/// Performs "signed ternary subtraction" which takes in an extra bit to subtract, and may return an
/// additional bit of overflow. This signed function is used only on the highest-ordered data,
/// for which the signed overflow result indicates whether the big integer overflowed or not.
#[inline(always)]
pub const fn borrowing_sub(lhs: u64, rhs: u64, borrow: bool) -> (u64, bool) {
    let (a, b) = lhs.overflowing_sub(rhs);
    let (c, d) = a.overflowing_sub(borrow as u64);
    (c, b != d)
}

/// Compute a + (b * c) + carry, returning the result and the new carry over.
#[inline(always)]
pub const fn mac(a: u64, b: u64, c: u64, carry: u64) -> (u64, u64) {
    let ret = (a as u128) + ((b as u128) * (c as u128)) + (carry as u128);
    (ret as u64, (ret >> 64) as u64)
}
/// Compute a << b | carry, returning the result and the new carry over.
#[inline(always)]
pub const fn slc(a: u64, b: u32, carry: u64) -> (u64, u64) {
    (a.overflowing_shl(b).0 | carry, a >> (64 - b))
}

macro_rules! impl_add_binop {
    ($lhs:ty, $rhs:ty) => {
        impl_add_binop!{{} {} {$lhs} {$rhs}}
    };
    ({$($gen:tt)*} {$(where $($wc:tt)+)?} {$($lhs:tt)+} {$($rhs:tt)+}) => {
        impl<'b, $($gen)*> core::ops::Add<&'b $($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            type Output = <&'b Self as core::ops::Add<&'b $($rhs)+>>::Output;

            #[inline]
            fn add(self, rhs: &'b $($rhs)+) -> Self::Output {
                &self + rhs
            }
        }

        impl<'a, $($gen)*> core::ops::Add<$($rhs)+> for &'a $($lhs)+
        $(where $($wc)+)? {
            type Output = <Self as core::ops::Add<&'a $($rhs)+>>::Output;

            #[inline]
            fn add(self, rhs: $($rhs)+) -> Self::Output {
                self + &rhs
            }
        }

        impl<$($gen)*> core::ops::Add<$($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            type Output = <&'static Self as core::ops::Add<&'static $($rhs)+>>::Output;

            #[inline]
            fn add(self, rhs: $($rhs)+) -> Self::Output {
                &self + &rhs
            }
        }
    };
}

macro_rules! impl_sub_binop {
    ($lhs:ty, $rhs:ty) => {
        impl_sub_binop!{{} {} {$lhs} {$rhs}}
    };
    ({$($gen:tt)*} {$(where $($wc:tt)+)?} {$($lhs:tt)+} {$($rhs:tt)+}) => {
        impl<'b, $($gen)*> core::ops::Sub<&'b $($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            type Output = <&'b Self as core::ops::Sub<&'b $($rhs)+>>::Output;

            #[inline]
            fn sub(self, rhs: &'b $($rhs)+) -> Self::Output {
                &self - rhs
            }
        }

        impl<'a, $($gen)*> core::ops::Sub<$($rhs)+> for &'a $($lhs)+
        $(where $($wc)+)? {
            type Output = <Self as core::ops::Sub<&'a $($rhs)+>>::Output;

            #[inline]
            fn sub(self, rhs: $($rhs)+) -> Self::Output {
                self - &rhs
            }
        }

        impl<$($gen)*> core::ops::Sub<$($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            type Output = <&'static Self as core::ops::Sub<&'static $($rhs)+>>::Output;

            #[inline]
            fn sub(self, rhs: $($rhs)+) -> Self::Output {
                &self - &rhs
            }
        }
    };
}

macro_rules! impl_binops_additive_output {
    ($lhs:ty, $rhs:ty) => {
        impl_add_binop!($lhs, $rhs);
        impl_sub_binop!($lhs, $rhs);
    };
    ({$($gen:tt)*} {$(where $($wc:tt)+)?} {$($lhs:tt)+} {$($rhs:tt)+}) => {
        impl_add_binop!({$($gen)*} {$(where $($wc)+)?} {$($lhs)+} {$($rhs)+});
        impl_sub_binop!({$($gen)*} {$(where $($wc)+)?} {$($lhs)+} {$($rhs)+});
    };
}

macro_rules! impl_binops_multiplicative_mixed {
    ($lhs:ident, $rhs:ident, $output:ident) => {
        impl<'b> core::ops::Mul<&'b $rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: &'b $rhs) -> $output {
                &self * rhs
            }
        }

        impl<'a> core::ops::Mul<$rhs> for &'a $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: $rhs) -> $output {
                self * &rhs
            }
        }

        impl core::ops::Mul<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: $rhs) -> $output {
                &self * &rhs
            }
        }
    };
    ({$($gen:tt)*} {$(where $($wc:tt)+)?} {$($lhs:tt)+} {$($rhs:tt)+} {$($output:tt)+}) => {
        impl<'b, $($gen)*> core::ops::Mul<&'b $($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            type Output = $($output)+;

            #[inline]
            fn mul(self, rhs: &'b $($rhs)+) -> $($output)+
            $(where $($wc)+)? {
                &self * rhs
            }
        }

        impl<'a, $($gen)*> core::ops::Mul<$($rhs)+> for &'a $($lhs)+
        $(where $($wc)+)? {
            type Output = $($output)+;

            #[inline]
            fn mul(self, rhs: $($rhs)+) -> $($output)+ {
                self * &rhs
            }
        }

        impl<$($gen)*> core::ops::Mul<$($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            type Output = $($output)+;

            #[inline]
            fn mul(self, rhs: $($rhs)+) -> $($output)+ {
                &self * &rhs
            }
        }
    };
}

macro_rules! impl_binops_additive {
    ($lhs:ident, $rhs:ident) => {
        impl_binops_additive!{{} {} {$lhs} {$rhs}}
    };
    ({$($gen:tt)*} {$(where $($wc:tt)+)?} {$($lhs:tt)+} {$($rhs:tt)+}) => {
        impl_binops_additive_output!({$($gen)*} {$(where $($wc)+)?} {$($lhs)+} {$($rhs)+});

        impl<$($gen)*> core::ops::SubAssign<$($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            #[inline]
            fn sub_assign(&mut self, rhs: $($rhs)+) {
                *self = &*self - &rhs;
            }
        }

        impl<$($gen)*> core::ops::AddAssign<$($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            #[inline]
            fn add_assign(&mut self, rhs: $($rhs)+) {
                *self = &*self + &rhs;
            }
        }

        impl<'b, $($gen)*> core::ops::SubAssign<&'b $($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            #[inline]
            fn sub_assign(&mut self, rhs: &'b $($rhs)+) {
                *self = &*self - rhs;
            }
        }

        impl<'b, $($gen)*> core::ops::AddAssign<&'b $($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            #[inline]
            fn add_assign(&mut self, rhs: &'b $($rhs)+) {
                *self = &*self + rhs;
            }
        }
    }
}

macro_rules! impl_binops_multiplicative {
    ($lhs:ident, $rhs:ident) => {
        impl_binops_multiplicative!{{} {} {$lhs} {$rhs}}
    };
    ({$($gen:tt)*} {$(where $($wc:tt)+)?} {$($lhs:tt)+} {$($rhs:tt)+}) => {
        impl_binops_multiplicative_mixed!({$($gen)*} {$(where $($wc)+)?} {$($lhs)+} {$($rhs)+} {$($lhs)+});

        impl<$($gen)*> MulAssign<$($rhs)+> for $($lhs)+ {
            #[inline]
            fn mul_assign(&mut self, rhs: $($rhs)+) {
                *self = &*self * &rhs;
            }
        }

        impl<'b, $($gen)*> MulAssign<&'b $($rhs)+> for $($lhs)+ {
            #[inline]
            fn mul_assign(&mut self, rhs: &'b $($rhs)+) {
                *self = &*self * rhs;
            }
        }
    }
}

macro_rules! be_bytes_to_u64 {
    ($b:ident[$i:literal..]) => {
        u64::from_be_bytes([$b[$i+0], $b[$i+1], $b[$i+2], $b[$i+3], $b[$i+4], $b[$i+5], $b[$i+6], $b[$i+7]])
    };
}

macro_rules! le_bytes_to_u64 {
    ($b:ident[$i:literal..]) => {
        u64::from_le_bytes([$b[$i+0], $b[$i+1], $b[$i+2], $b[$i+3], $b[$i+4], $b[$i+5], $b[$i+6], $b[$i+7]])
    };
}

#[inline(always)]
pub const fn copy_bytes<const A: usize, const V: usize>(mut a: [u8; A], offset: usize, v: [u8; V]) -> [u8; A] {
    let mut i = 0;
    while i < V {
        a[offset + i] = v[i];
        i += 1;
    }
    a
}

// Hack to get the ! type on stable
#[doc(hidden)]
pub trait HasOutput {
    type Output;
}
impl<O> HasOutput for fn() -> O {
    type Output = O;
}
pub type Never = <fn() -> ! as HasOutput>::Output;

#[doc(hidden)]
pub trait NonZero {}

#[doc(hidden)]
pub trait OtherMag {
    const MAGNITUDE: usize;
    type Mag<const MAGNITUDE: usize>: OtherMag;
}

#[doc(hidden)]
pub trait Mag<const ELEMS: usize, Data>: Sized {
    type Prev: Mag<ELEMS, Data>;
    type Next: Mag<ELEMS, Data>;

    /// A multiple of the prime that is larger than this element could be
    const MODULUS: Data;

    fn make(v: [Data; ELEMS]) -> Self;
    fn data(&self) -> [&Data; ELEMS];
    /// Negates an element by subtracting it from the `Self::MODULUS`
    fn negate(&self) -> Self;
}

impl OtherMag for Never {
    const MAGNITUDE: usize = unimplemented!();
    type Mag<const MAGNITUDE: usize> = Never;
}

impl<const ELEMS: usize, Data> Mag<ELEMS, Data> for Never {
    type Prev = Never;
    type Next = Never;

    const MODULUS: Data = unimplemented!();

    #[inline(always)]
    fn make(_: [Data; ELEMS]) -> Self {
        unimplemented!()
    }
    #[inline(always)]
    fn data(&self) -> [&Data; ELEMS] {
        unreachable!()
    }
    #[inline(always)]
    fn negate(&self) -> Self {
        unreachable!()
    }
}

pub trait Ops<const ELEMS: usize, Data, Rhs> {
    type OpOut: Mag<ELEMS, Data>;
    fn add(lhs: &Self, rhs: &Rhs) -> Self::OpOut;
    fn sub(lhs: &Self, rhs: &Rhs) -> Self::OpOut;
}

pub trait DoubleOp<const POW: usize = 0> {
    type DoubleOut;
    fn double(lhs: &Self) -> Self::DoubleOut;
}

pub trait MontOp {
    type MontOut;
    fn montgomery_reduce(lhs: &Self) -> Self::MontOut;
}

pub trait MulOp<const MAG: usize>: OtherMag {
    type MulOut;
    fn mul(lhs: &Self, rhs: &Self::Mag<MAG>) -> Self::MulOut;
}

pub trait SquareOp: OtherMag {
    type SquareOut;
    fn square(lhs: &Self) -> Self::SquareOut;
}


#[derive(Debug, Clone, Copy)]
pub struct FpMag<const MAG: usize>;

pub trait RawMagnitude: Copy {
    const MAG: usize;
    type GtEq<R: RawMagnitude, LVal: RawMagnitude, RVal: RawMagnitude>: RawMagnitude;
    type Plus1: RawMagnitude;
    type PlusR<R: RawMagnitude>: RawMagnitude;
    type Double: RawMagnitude;
    /// Returns `R << Self`
    type LshR<R: RawMagnitude>: RawMagnitude;
    type Mul<R: RawMagnitude>: RawMagnitude;
    type Montgomery: RawMagnitude;
    type AsFp: FpMagnitude;
    type AsFpWide: FpWideMagnitude;
}
pub trait FpMagnitude : RawMagnitude {}
pub trait FpWideMagnitude : RawMagnitude {}

impl RawMagnitude for Never {
    const MAG: usize = unimplemented!();
    type GtEq<R: RawMagnitude, LVal: RawMagnitude, RVal: RawMagnitude> = Never;
    type Plus1 = Never;
    type PlusR<R: RawMagnitude> = Never;
    type Double = Never;
    type LshR<R: RawMagnitude> = Never;
    type Mul<R: RawMagnitude> = Never;
    type Montgomery = Never;
    type AsFp = Never;
    type AsFpWide = Never;
}
impl FpMagnitude for Never {}
impl FpWideMagnitude for Never {}

impl RawMagnitude for FpMag<0> {
    const MAG: usize = 0;
    type GtEq<R: RawMagnitude, LVal: RawMagnitude, RVal: RawMagnitude> = RVal;
    type Plus1 = FpMag<1>;
    type PlusR<R: RawMagnitude> = R::Plus1;
    type Double = FpMag<1>;
    type LshR<R: RawMagnitude> = R;
    type Mul<R: RawMagnitude> = R;
    type Montgomery = FpMag<{(0+13)/10}>;
    type AsFp = FpMag<0>;
    type AsFpWide = FpMag<0>;
}
impl FpMagnitude for FpMag<0> {}
impl FpWideMagnitude for FpMag<0> {}

pub trait Iif<const COND: bool, True, False> {
    type Value;
}

impl<True, False> Iif<false, True, False> for () {
    type Value = False;
}
impl<True, False> Iif<true, True, False> for () {
    type Value = True;
}

macro_rules! raw_magnitude {
    ($($i:literal)+) => {$(
impl RawMagnitude for FpMag<$i> {
    const MAG: usize = $i;
    type GtEq<R: RawMagnitude, LVal: RawMagnitude, RVal: RawMagnitude> = R::GtEq<FpMag<{$i-1}>, RVal, LVal>;
    type Plus1 = <() as Iif<{$i*2 <= 191}, 
        FpMag<{$i+1}>,
        Never,
    >>::Value;
    type PlusR<R: RawMagnitude> = <<FpMag<{$i-1}> as RawMagnitude>::PlusR<R> as RawMagnitude>::Plus1;
    type Mul<R: RawMagnitude> = <<FpMag<{$i-1}> as RawMagnitude>::Mul<R> as RawMagnitude>::PlusR<R>;
    type Double = <() as Iif<{$i*2 <= 191}, 
        FpMag<{($i+1)*2-1}>,
        Never,
    >>::Value;
    type LshR<R: RawMagnitude> = <<FpMag<{$i-1}> as RawMagnitude>::LshR<R> as RawMagnitude>::Double;
    type Montgomery = FpMag<{($i+12)/10}>;
    type AsFp = <() as Iif<{$i <= 16}, FpMag<{
        let mut v = $i;
        while v > 8 {
            v = v / 2;
        }
        v
    }>, Never>>::Value;
    type AsFpWide = FpMag<{
        let mut v = $i;
        while v > 95 {
            v = v / 2;
        }
        v
    }>;
}
    )+};
}
macro_rules! fp_magnitude {
    ($($i:literal)+) => {$(
impl FpMagnitude for FpMag<$i> {}
    )+};
}
macro_rules! fp_wide_magnitude {
    ($($i:literal)+) => {$(
impl FpWideMagnitude for FpMag<$i> {}
    )+};
}

raw_magnitude!{1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90 91 92 93 94 95 96 97 98 99 100 101 102 103 104 105 106 107 108 109 110 111 112 113 114 115 116 117 118 119 120 121 122 123 124 125 126 127 128 129 130 131 132 133 134 135 136 137 138 139 140 141 142 143 144 145 146 147 148 149 150 151 152 153 154 155 156 157 158 159 160 161 162 163 164 165 166 167 168 169 170 171 172 173 174 175 176 177 178 179 180 181 182 183 184 185 186 187 188 189 190 191}
fp_magnitude!{1 2 3 4 5 6 7 8}
fp_wide_magnitude!{1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90 91 92 93 94 95}

pub type MagDouble<Mag> = <Mag as RawMagnitude>::Double;
pub type MagLsh<Mag, const P: usize> = <FpMag<P> as RawMagnitude>::LshR<Mag>;
pub type MagAdd<Lhs, Rhs> = <Lhs as RawMagnitude>::PlusR<Rhs>;
pub type MagSub<Lhs, Rhs> = <Lhs as RawMagnitude>::GtEq<Rhs, Lhs, Rhs>;
pub type MagSquare<Mag> = <Mag as RawMagnitude>::Mul<Mag>;
pub type MagMul<Lhs, Rhs> = <Lhs as RawMagnitude>::Mul<Rhs>;
pub type MagReduce<Mag> = <Mag as RawMagnitude>::Montgomery;
pub type MagFp<Mag> = <Mag as RawMagnitude>::AsFp;
pub type MagFpWide<Mag> = <Mag as RawMagnitude>::AsFpWide;

pub trait Timing: Copy + fmt::Debug {
    const VAR: bool;
    type Choice: Copy + fmt::Debug;
    fn to_bool(v: Self::Choice) -> bool;
    fn to_choice(v: Self::Choice) -> Choice;
    fn from_bool(v: bool) -> Self::Choice;
    fn from_choice(v: Choice) -> Self::Choice;
}

#[derive(Debug, Clone, Copy)]
pub struct VarTime;
#[derive(Debug, Clone, Copy)]
pub struct ConstTime;

impl Timing for VarTime {
    const VAR: bool = true;
    type Choice = bool;
    fn to_bool(v: Self::Choice) -> bool {
        v
    }
    fn to_choice(v: Self::Choice) -> Choice {
        Choice::from(v as u8)
    }
    fn from_bool(v: bool) -> Self::Choice {
        v
    }
    fn from_choice(v: Choice) -> Self::Choice {
        v.into()
    }
}

impl Timing for ConstTime {
    const VAR: bool = false;
    type Choice = Choice;
    fn to_bool(v: Self::Choice) -> bool {
        v.into()
    }
    fn to_choice(v: Self::Choice) -> Choice {
        v
    }
    fn from_bool(v: bool) -> Self::Choice {
        Choice::from(v as u8)
    }
    fn from_choice(v: Choice) -> Self::Choice {
        v
    }
}

pub trait Precompute {
    const W: u32;
}

macro_rules! precomp {
    ($($i:literal)+) => {$(
impl Precompute for FpMag<{1 << $i}> {
    const W: u32 = $i + 2;
}
    )+};
}

precomp!{0 1 2 3 4 5 6 7 8 9 10}

#[cfg(test)]
mod test {
    use super::{FpMag, RawMagnitude};

    #[test]
    fn test_max() {
        assert_eq!(<<FpMag<10> as RawMagnitude>::GtEq<FpMag::<9>, FpMag::<10>, FpMag::<9>> as RawMagnitude>::MAG, 10);
        assert_eq!(<<FpMag<10> as RawMagnitude>::GtEq<FpMag::<9>, FpMag::<1>, FpMag::<5>> as RawMagnitude>::MAG, 1);
    }

    #[test]
    fn test_add() {
        assert_eq!(<<FpMag<0> as RawMagnitude>::PlusR<FpMag::<9>> as RawMagnitude>::MAG, 10);
        assert_eq!(<<FpMag<1> as RawMagnitude>::PlusR<FpMag::<8>> as RawMagnitude>::MAG, 10);
        assert_eq!(<<FpMag<2> as RawMagnitude>::PlusR<FpMag::<7>> as RawMagnitude>::MAG, 10);
        assert_eq!(<<FpMag<3> as RawMagnitude>::PlusR<FpMag::<6>> as RawMagnitude>::MAG, 10);
        assert_eq!(<<FpMag<4> as RawMagnitude>::PlusR<FpMag::<5>> as RawMagnitude>::MAG, 10);
        assert_eq!(<<FpMag<5> as RawMagnitude>::PlusR<FpMag::<4>> as RawMagnitude>::MAG, 10);
        assert_eq!(<<FpMag<6> as RawMagnitude>::PlusR<FpMag::<3>> as RawMagnitude>::MAG, 10);
        assert_eq!(<<FpMag<7> as RawMagnitude>::PlusR<FpMag::<2>> as RawMagnitude>::MAG, 10);
        assert_eq!(<<FpMag<8> as RawMagnitude>::PlusR<FpMag::<1>> as RawMagnitude>::MAG, 10);
        assert_eq!(<<FpMag<9> as RawMagnitude>::PlusR<FpMag::<0>> as RawMagnitude>::MAG, 10);
    }

    #[test]
    fn test_mul() {
        assert_eq!(<<FpMag<0> as RawMagnitude>::Mul<FpMag::<9>> as RawMagnitude>::MAG, 9);
        assert_eq!(<<FpMag<1> as RawMagnitude>::Mul<FpMag::<8>> as RawMagnitude>::MAG, 17);
        assert_eq!(<<FpMag<2> as RawMagnitude>::Mul<FpMag::<7>> as RawMagnitude>::MAG, 23);
        assert_eq!(<<FpMag<3> as RawMagnitude>::Mul<FpMag::<6>> as RawMagnitude>::MAG, 27);
        assert_eq!(<<FpMag<4> as RawMagnitude>::Mul<FpMag::<5>> as RawMagnitude>::MAG, 29);
        assert_eq!(<<FpMag<5> as RawMagnitude>::Mul<FpMag::<4>> as RawMagnitude>::MAG, 29);
        assert_eq!(<<FpMag<6> as RawMagnitude>::Mul<FpMag::<3>> as RawMagnitude>::MAG, 27);
        assert_eq!(<<FpMag<7> as RawMagnitude>::Mul<FpMag::<2>> as RawMagnitude>::MAG, 23);
        assert_eq!(<<FpMag<8> as RawMagnitude>::Mul<FpMag::<1>> as RawMagnitude>::MAG, 17);
        assert_eq!(<<FpMag<9> as RawMagnitude>::Mul<FpMag::<0>> as RawMagnitude>::MAG, 9);
    }
}
