use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::vec4::Vec4;

pub mod ops;
pub mod det_advanced;
pub mod adjugate;
pub mod det_transpose;

verus! {

pub struct Mat4x4<T: Ring> {
    pub row0: Vec4<T>,
    pub row1: Vec4<T>,
    pub row2: Vec4<T>,
    pub row3: Vec4<T>,
}

} // verus!
