#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::vec2::Vec2;
#[cfg(verus_keep_ghost)]
use crate::vec2::ops::{scale, dot, norm_sq, lerp};
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

pub struct RuntimeVec2<R, V: Ring> where R: RuntimeRingOps<V> {
    pub x: R,
    pub y: R,
    pub model: Ghost<Vec2<V>>,
}

impl<R: RuntimeRingOps<V>, V: Ring> RuntimeVec2<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.x@ == self.model@.x
        &&& self.y@ == self.model@.y
    }

    pub fn new(x: R, y: R) -> (out: Self)
        requires x.wf_spec(), y.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == x@,
            out.model@.y == y@,
    {
        let ghost model = Vec2 { x: x@, y: y@ };
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    pub fn add(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.add(rhs.model@),
    {
        let x = self.x.add(&rhs.x);
        let y = self.y.add(&rhs.y);
        let ghost model = self.model@.add(rhs.model@);
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    pub fn sub(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.sub(rhs.model@),
    {
        let x = self.x.sub(&rhs.x);
        let y = self.y.sub(&rhs.y);
        let ghost model = self.model@.sub(rhs.model@);
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    pub fn neg(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.neg(),
    {
        let x = self.x.neg();
        let y = self.y.neg();
        let ghost model = self.model@.neg();
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    pub fn zero(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@ == <Vec2<V> as AdditiveCommutativeMonoid>::zero(),
    {
        let x = self.x.zero_like();
        let y = self.y.zero_like();
        let ghost model: Vec2<V> = <Vec2<V> as AdditiveCommutativeMonoid>::zero();
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    pub fn scale(s: &R, v: &Self) -> (out: Self)
        requires s.wf_spec(), v.wf_spec(),
        ensures out.wf_spec(), out.model@ == scale::<V>(s@, v.model@),
    {
        let x = s.mul(&v.x);
        let y = s.mul(&v.y);
        let ghost model = scale::<V>(s@, v.model@);
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    pub fn dot(&self, rhs: &Self) -> (out: R)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out@ == dot::<V>(self.model@, rhs.model@),
    {
        self.x.mul(&rhs.x).add(&self.y.mul(&rhs.y))
    }

    pub fn norm_sq(&self) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out@ == norm_sq::<V>(self.model@),
    {
        self.dot(self)
    }

    ///  Instance scalar multiply: self * s.
    pub fn scaled(&self, s: &R) -> (out: Self)
        requires self.wf_spec(), s.wf_spec(),
        ensures out.wf_spec(), out.model@ == scale::<V>(s@, self.model@),
    {
        Self::scale(s, self)
    }

    pub fn lerp(&self, other: &Self, t: &R) -> (out: Self)
        requires self.wf_spec(), other.wf_spec(), t.wf_spec(),
        ensures out.wf_spec(), out.model@ == lerp::<V>(self.model@, other.model@, t@),
    {
        let one = t.one_like();
        let one_minus_t = one.sub(t);
        let sa = Self::scale(&one_minus_t, self);
        let sb = Self::scale(t, other);
        sa.add(&sb)
    }
}

} //  verus!
