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
    ({$($lc:ident $rc:ident)?} {$(where $($wc:tt)+)?} {$($lhs:tt)+} {$($rhs:tt)+}) => {
        impl<'b, $(const $lc: usize, const $rc: usize)?> Add<&'b $($rhs)+$(<$rc>)?> for $($lhs)+$(<$lc>)?
        $(where $($wc)+)? {
            type Output = <&'b Self as Add<&'b $($rhs)+$(<$rc>)?>>::Output;

            #[inline]
            fn add(self, rhs: &'b $($rhs)+$(<$rc>)?) -> Self::Output {
                &self + rhs
            }
        }

        impl<'a, $(const $lc: usize, const $rc: usize)?> Add<$($rhs)+$(<$rc>)?> for &'a $($lhs)+$(<$lc>)?
        $(where $($wc)+)? {
            type Output = <Self as Add<&'a $($rhs)+$(<$rc>)?>>::Output;

            #[inline]
            fn add(self, rhs: $($rhs)+$(<$rc>)?) -> Self::Output {
                self + &rhs
            }
        }

        impl<$(const $lc: usize, const $rc: usize)?> Add<$($rhs)+$(<$rc>)?> for $($lhs)+$(<$lc>)?
        $(where $($wc)+)? {
            type Output = <&'static Self as Add<&'static $($rhs)+$(<$rc>)?>>::Output;

            #[inline]
            fn add(self, rhs: $($rhs)+$(<$rc>)?) -> Self::Output {
                &self + &rhs
            }
        }
    };
}

macro_rules! impl_sub_binop {
    ($lhs:ty, $rhs:ty) => {
        impl_sub_binop!{{} {} {$lhs} {$rhs}}
    };
    ({$($lc:ident $rc:ident)?} {$(where $($wc:tt)+)?} {$($lhs:tt)+} {$($rhs:tt)+}) => {
        impl<'b, $(const $lc: usize, const $rc: usize)?> Sub<&'b $($rhs)+$(<$rc>)?> for $($lhs)+$(<$lc>)?
        $(where $($wc)+)? {
            type Output = <&'b Self as Sub<&'b $($rhs)+$(<$rc>)?>>::Output;

            #[inline]
            fn sub(self, rhs: &'b $($rhs)+$(<$rc>)?) -> Self::Output {
                &self - rhs
            }
        }

        impl<'a, $(const $lc: usize, const $rc: usize)?> Sub<$($rhs)+$(<$rc>)?> for &'a $($lhs)+$(<$lc>)?
        $(where $($wc)+)? {
            type Output = <Self as Sub<&'a $($rhs)+$(<$rc>)?>>::Output;

            #[inline]
            fn sub(self, rhs: $($rhs)+$(<$rc>)?) -> Self::Output {
                self - &rhs
            }
        }

        impl<$(const $lc: usize, const $rc: usize)?> Sub<$($rhs)+$(<$rc>)?> for $($lhs)+$(<$lc>)?
        $(where $($wc)+)? {
            type Output = <&'static Self as Sub<&'static $($rhs)+$(<$rc>)?>>::Output;

            #[inline]
            fn sub(self, rhs: $($rhs)+$(<$rc>)?) -> Self::Output {
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
    ({$lc:ident $rc:ident} {where $($wc:tt)+} {$($lhs:tt)+} {$($rhs:tt)+}) => {
        impl_add_binop!({$lc $rc} {where $($wc)+} {$($lhs)+} {$($rhs)+});
        impl_sub_binop!({$lc $rc} {where $($wc)+} {$($lhs)+} {$($rhs)+});
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
}

macro_rules! impl_binops_additive {
    ($lhs:ident, $rhs:ident) => {
        impl_binops_additive_output!($lhs, $rhs);

        impl SubAssign<$rhs> for $lhs {
            #[inline]
            fn sub_assign(&mut self, rhs: $rhs) {
                *self = &*self - &rhs;
            }
        }

        impl AddAssign<$rhs> for $lhs {
            #[inline]
            fn add_assign(&mut self, rhs: $rhs) {
                *self = &*self + &rhs;
            }
        }

        impl<'b> SubAssign<&'b $rhs> for $lhs {
            #[inline]
            fn sub_assign(&mut self, rhs: &'b $rhs) {
                *self = &*self - rhs;
            }
        }

        impl<'b> AddAssign<&'b $rhs> for $lhs {
            #[inline]
            fn add_assign(&mut self, rhs: &'b $rhs) {
                *self = &*self + rhs;
            }
        }
    };
}

macro_rules! impl_binops_multiplicative {
    ($lhs:ident, $rhs:ident) => {
        impl_binops_multiplicative_mixed!($lhs, $rhs, $lhs);

        impl MulAssign<$rhs> for $lhs {
            #[inline]
            fn mul_assign(&mut self, rhs: $rhs) {
                *self = &*self * &rhs;
            }
        }

        impl<'b> MulAssign<&'b $rhs> for $lhs {
            #[inline]
            fn mul_assign(&mut self, rhs: &'b $rhs) {
                *self = &*self * rhs;
            }
        }
    };
}
