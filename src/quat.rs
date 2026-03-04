use vstd::prelude::*;
use verus_algebra::traits::*;

pub mod algebra;
pub mod ops;
pub mod basis;
pub mod assoc;
pub mod conjugate;
pub mod norm;
pub mod inverse;
pub mod rotation;

verus! {

pub struct Quat<T: Ring> {
    pub w: T,
    pub x: T,
    pub y: T,
    pub z: T,
}

impl<T: Ring> Quat<T> {
    pub open spec fn new(w: T, x: T, y: T, z: T) -> Self {
        Quat { w, x, y, z }
    }
}

} // verus!
