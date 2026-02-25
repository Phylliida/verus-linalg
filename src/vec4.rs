use vstd::prelude::*;
use verus_algebra::traits::*;

pub mod algebra;
pub mod ops;

verus! {

pub struct Vec4<T: Ring> {
    pub x: T,
    pub y: T,
    pub z: T,
    pub w: T,
}

impl<T: Ring> Vec4<T> {
    pub open spec fn new(x: T, y: T, z: T, w: T) -> Self {
        Vec4 { x, y, z, w }
    }
}

} // verus!
