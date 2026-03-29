use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::vec2::Vec2;

pub mod algebra;
pub mod ops;

verus! {

pub struct Mat2x2<T: Ring> {
    pub row0: Vec2<T>,
    pub row1: Vec2<T>,
}

} //  verus!
