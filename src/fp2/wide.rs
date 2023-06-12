use crate::{fp::wide::FpWide, util::{MulOp, SquareOp, Ops, OtherMag}};

use super::Fp2;

#[derive(Copy, Clone)]
pub struct Fp2Wide<const MAGNITUDE: usize, const VARTIME: bool> {
    pub c0: FpWide<MAGNITUDE, VARTIME>,
    pub c1: FpWide<MAGNITUDE, VARTIME>,
}

impl<const MAGNITUDE: usize, const VARTIME: bool> OtherMag for Fp2Wide<MAGNITUDE, VARTIME> {
    type Mag<const MAG2: usize> = Fp2Wide<MAG2, VARTIME>;
}

macro_rules! mul_helper {
    ($ua:literal {$($ub:literal)*}) => {
// $(
// impl<const VARTIME: bool> MulOp<[u64; 6], $ub> for Fp2<$ua, VARTIME> {
//     type MulOut = Fp2Wide<{($ua+1)*($ub+1)-1}, VARTIME>;
//     fn mul(lhs: &Self, rhs: &Self::Mag<$ub>) -> Self::MulOut {
//         Fp2Wide(mul_wide(&lhs.0, &rhs.0))
//     }
// })*
impl<const VARTIME: bool> SquareOp<(Fp<$ua, VARTIME>, Fp<$ua, VARTIME>)> for Fp2<$ua, VARTIME> {
    type SquareOut = Fp2Wide<{($ua+1)*($ua+1)-1}, VARTIME>;
    fn square(lhs: &Self) -> Self::SquareOut {
        let a = Ops::add(&lhs.c0, &lhs.c1);
        let b = Ops::sub(&lhs.c0, &lhs.c1);
        let c = Ops::add(&lhs.c0, &lhs.c0);

        Fp2Wide {
            c0: MulOp::mul(&a, &b),
            c1: MulOp::mul(&c, &lhs.c1),
        }
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

// mul_impl!{0,1,2,3,4,5,6,7,8}
