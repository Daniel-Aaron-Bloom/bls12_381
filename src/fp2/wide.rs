use core::fmt;
use subtle::{Choice, ConstantTimeEq};

use crate::{fp::wide::{FpWide, FpAWide, FpWideReduce}, util::{OtherMag, FpWideMagnitude, RawMagnitude, Timing}};

use super::{Fp2A};

#[derive(Copy, Clone)]
pub struct Fp2Wide<const MAGNITUDE: usize, const VARTIME: bool> {
    pub c0: FpWide<MAGNITUDE, VARTIME>,
    pub c1: FpWide<MAGNITUDE, VARTIME>,
}

#[derive(Copy, Clone)]
pub struct Fp2AWide<Mag0: FpWideMagnitude, Mag1: FpWideMagnitude, T: Timing> {
    pub c0: FpAWide<Mag0, T>,
    pub c1: FpAWide<Mag1, T>,
}

impl<const MAGNITUDE: usize, const VARTIME: bool> OtherMag for Fp2Wide<MAGNITUDE, VARTIME> {
    const MAGNITUDE: usize = MAGNITUDE;
    type Mag<const MAG2: usize> = Fp2Wide<MAG2, VARTIME>;
}

impl<Mag0: FpWideMagnitude, Mag1: FpWideMagnitude, T: Timing> fmt::Debug for Fp2AWide<Mag0, Mag1, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?} + {:?}*u", self.c0, self.c1)
    }
}

impl<Mag0: FpWideMagnitude, Mag1: FpWideMagnitude, T: Timing> ConstantTimeEq for Fp2AWide<Mag0, Mag1, T> {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.c0.ct_eq(&other.c0) & self.c1.ct_eq(&other.c1)
    }
}

impl<Mag0: FpWideMagnitude, Mag1: FpWideMagnitude, T: Timing> Eq for Fp2AWide<Mag0, Mag1, T> {}
impl<Mag0: FpWideMagnitude, Mag1: FpWideMagnitude, T: Timing> PartialEq for Fp2AWide<Mag0, Mag1, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if T::VAR {
            self.c0 == other.c0 && self.c1 == other.c1
        } else {
            bool::from(self.ct_eq(other))
        }
    }
}

impl<Mag0: FpWideMagnitude, Mag1: FpWideMagnitude, T: Timing> Fp2AWide<Mag0, Mag1, T> {

    #[inline(always)]
    pub const fn vartime<T2: Timing>(self) -> Fp2AWide<Mag0, Mag1, T2> {
        Fp2AWide{
            c0: self.c0.vartime(),
            c1: self.c1.vartime(),
        }
    }

    #[inline(always)]
    pub const fn mag<MagR0, MagR1>(self) -> Fp2AWide<MagR0, MagR1, T>
    where MagR0: FpWideMagnitude, MagR1: FpWideMagnitude {
        Fp2AWide{
            c0: self.c0.mag(),
            c1: self.c1.mag(),
        }
    }

    pub const fn montgomery_reduce(&self) -> Fp2A<FpWideReduce<Mag0>, FpWideReduce<Mag1>, T> {
        let v = (Mag0::MAG, Mag1::MAG, FpWideReduce::<Mag0>::MAG, FpWideReduce::<Mag1>::MAG);
        Fp2A {
            c0: self.c0.montgomery_reduce(),
            c1: self.c1.montgomery_reduce(),
        }
    }
}
