use vstd::prelude::*;
use verus_algebra::traits::*;

pub mod algebra;
pub mod ops;

verus! {

pub struct Vec3<T: Ring> {
    pub x: T,
    pub y: T,
    pub z: T,
}

impl<T: Ring> Vec3<T> {
    pub open spec fn new(x: T, y: T, z: T) -> Self {
        Vec3 { x, y, z }
    }
}

} // verus!
