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
        impl<'b, $($gen)*> Add<&'b $($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            type Output = <&'b Self as Add<&'b $($rhs)+>>::Output;

            #[inline]
            fn add(self, rhs: &'b $($rhs)+) -> Self::Output {
                &self + rhs
            }
        }

        impl<'a, $($gen)*> Add<$($rhs)+> for &'a $($lhs)+
        $(where $($wc)+)? {
            type Output = <Self as Add<&'a $($rhs)+>>::Output;

            #[inline]
            fn add(self, rhs: $($rhs)+) -> Self::Output {
                self + &rhs
            }
        }

        impl<$($gen)*> Add<$($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            type Output = <&'static Self as Add<&'static $($rhs)+>>::Output;

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
        impl<'b, $($gen)*> Sub<&'b $($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            type Output = <&'b Self as Sub<&'b $($rhs)+>>::Output;

            #[inline]
            fn sub(self, rhs: &'b $($rhs)+) -> Self::Output {
                &self - rhs
            }
        }

        impl<'a, $($gen)*> Sub<$($rhs)+> for &'a $($lhs)+
        $(where $($wc)+)? {
            type Output = <Self as Sub<&'a $($rhs)+>>::Output;

            #[inline]
            fn sub(self, rhs: $($rhs)+) -> Self::Output {
                self - &rhs
            }
        }

        impl<$($gen)*> Sub<$($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            type Output = <&'static Self as Sub<&'static $($rhs)+>>::Output;

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
        impl<'b> Mul<&'b $rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: &'b $rhs) -> $output {
                &self * rhs
            }
        }

        impl<'a> Mul<$rhs> for &'a $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: $rhs) -> $output {
                self * &rhs
            }
        }

        impl Mul<$rhs> for $lhs {
            type Output = $output;

            #[inline]
            fn mul(self, rhs: $rhs) -> $output {
                &self * &rhs
            }
        }
    };
    ({$($gen:tt)*} {$(where $($wc:tt)+)?} {$($lhs:tt)+} {$($rhs:tt)+} {$($output:tt)+}) => {
        impl<'b, $($gen)*> Mul<&'b $($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            type Output = $($output)+;

            #[inline]
            fn mul(self, rhs: &'b $($rhs)+) -> $($output)+
            $(where $($wc)+)? {
                &self * rhs
            }
        }

        impl<'a, $($gen)*> Mul<$($rhs)+> for &'a $($lhs)+
        $(where $($wc)+)? {
            type Output = $($output)+;

            #[inline]
            fn mul(self, rhs: $($rhs)+) -> $($output)+ {
                self * &rhs
            }
        }

        impl<$($gen)*> Mul<$($rhs)+> for $($lhs)+
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

        impl<$($gen)*> SubAssign<$($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            #[inline]
            fn sub_assign(&mut self, rhs: $($rhs)+) {
                *self = &*self - &rhs;
            }
        }

        impl<$($gen)*> AddAssign<$($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            #[inline]
            fn add_assign(&mut self, rhs: $($rhs)+) {
                *self = &*self + &rhs;
            }
        }

        impl<'b, $($gen)*> SubAssign<&'b $($rhs)+> for $($lhs)+
        $(where $($wc)+)? {
            #[inline]
            fn sub_assign(&mut self, rhs: &'b $($rhs)+) {
                *self = &*self - rhs;
            }
        }

        impl<'b, $($gen)*> AddAssign<&'b $($rhs)+> for $($lhs)+
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

pub trait Ops<const ELEMS: usize, Data, const MAG: usize>: OtherMag {
    type OpOut: Mag<ELEMS, Data>;
    fn add(lhs: &Self, rhs: &Self::Mag<MAG>) -> Self::OpOut;
    fn sub(lhs: &Self, rhs: &Self::Mag<MAG>) -> Self::OpOut;
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


trait Vartime {

}