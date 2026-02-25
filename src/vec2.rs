use vstd::prelude::*;
use verus_algebra::traits::*;

pub mod algebra;
pub mod ops;

verus! {

pub struct Vec2<T: Ring> {
    pub x: T,
    pub y: T,
}

impl<T: Ring> Vec2<T> {
    pub open spec fn new(x: T, y: T) -> Self {
        Vec2 { x, y }
    }
}

} // verus!
