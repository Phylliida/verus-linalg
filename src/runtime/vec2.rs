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
        &&& self.x.model() == self.model@.x
        &&& self.y.model() == self.model@.y
    }

    pub fn new(x: R, y: R) -> (out: Self)
        requires x.wf_spec(), y.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == x.model(),
            out.model@.y == y.model(),
    {
        let ghost model = Vec2 { x: x.model(), y: y.model() };
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    pub fn add_exec(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.add(rhs.model@),
    {
        let x = self.x.add(&rhs.x);
        let y = self.y.add(&rhs.y);
        let ghost model = self.model@.add(rhs.model@);
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    pub fn sub_exec(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.sub(rhs.model@),
    {
        let x = self.x.sub(&rhs.x);
        let y = self.y.sub(&rhs.y);
        let ghost model = self.model@.sub(rhs.model@);
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    pub fn neg_exec(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.neg(),
    {
        let x = self.x.neg();
        let y = self.y.neg();
        let ghost model = self.model@.neg();
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    pub fn zero_exec(&self) -> (out: Self)
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

    pub fn scale_exec(s: &R, v: &Self) -> (out: Self)
        requires s.wf_spec(), v.wf_spec(),
        ensures out.wf_spec(), out.model@ == scale::<V>(s.model(), v.model@),
    {
        let x = s.mul(&v.x);
        let y = s.mul(&v.y);
        let ghost model = scale::<V>(s.model(), v.model@);
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    pub fn dot_exec(&self, rhs: &Self) -> (out: R)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model() == dot::<V>(self.model@, rhs.model@),
    {
        self.x.mul(&rhs.x).add(&self.y.mul(&rhs.y))
    }

    pub fn norm_sq_exec(&self) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model() == norm_sq::<V>(self.model@),
    {
        self.dot_exec(self)
    }

    pub fn lerp_exec(&self, other: &Self, t: &R) -> (out: Self)
        requires self.wf_spec(), other.wf_spec(), t.wf_spec(),
        ensures out.wf_spec(), out.model@ == lerp::<V>(self.model@, other.model@, t.model()),
    {
        let one = t.one_like();
        let one_minus_t = one.sub(t);
        let sa = Self::scale_exec(&one_minus_t, self);
        let sb = Self::scale_exec(t, other);
        sa.add_exec(&sb)
    }
}

} //  verus!
