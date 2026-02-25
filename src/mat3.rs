use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::vec3::Vec3;

pub mod ops;

verus! {

pub struct Mat3x3<T: Ring> {
    pub row0: Vec3<T>,
    pub row1: Vec3<T>,
    pub row2: Vec3<T>,
}

} // verus!
