#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::vec4::Vec4;
#[cfg(verus_keep_ghost)]
use crate::vec4::ops::{scale, dot, norm_sq, lerp};
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

pub struct RuntimeVec4<R, V: Ring> where R: RuntimeRingOps<V> {
    pub x: R,
    pub y: R,
    pub z: R,
    pub w: R,
    pub model: Ghost<Vec4<V>>,
}

impl<R: RuntimeRingOps<V>, V: Ring> RuntimeVec4<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.z.wf_spec()
        &&& self.w.wf_spec()
        &&& self.x.model() == self.model@.x
        &&& self.y.model() == self.model@.y
        &&& self.z.model() == self.model@.z
        &&& self.w.model() == self.model@.w
    }

    pub fn new(x: R, y: R, z: R, w: R) -> (out: Self)
        requires x.wf_spec(), y.wf_spec(), z.wf_spec(), w.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == x.model(),
            out.model@.y == y.model(),
            out.model@.z == z.model(),
            out.model@.w == w.model(),
    {
        let ghost model = Vec4 { x: x.model(), y: y.model(), z: z.model(), w: w.model() };
        RuntimeVec4 { x, y, z, w, model: Ghost(model) }
    }

    pub fn add_exec(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.add(rhs.model@),
    {
        let ghost model = self.model@.add(rhs.model@);
        RuntimeVec4 {
            x: self.x.add(&rhs.x), y: self.y.add(&rhs.y),
            z: self.z.add(&rhs.z), w: self.w.add(&rhs.w),
            model: Ghost(model),
        }
    }

    pub fn sub_exec(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.sub(rhs.model@),
    {
        let ghost model = self.model@.sub(rhs.model@);
        RuntimeVec4 {
            x: self.x.sub(&rhs.x), y: self.y.sub(&rhs.y),
            z: self.z.sub(&rhs.z), w: self.w.sub(&rhs.w),
            model: Ghost(model),
        }
    }

    pub fn neg_exec(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.neg(),
    {
        let ghost model = self.model@.neg();
        RuntimeVec4 {
            x: self.x.neg(), y: self.y.neg(),
            z: self.z.neg(), w: self.w.neg(),
            model: Ghost(model),
        }
    }

    pub fn scale_exec(s: &R, v: &Self) -> (out: Self)
        requires s.wf_spec(), v.wf_spec(),
        ensures out.wf_spec(), out.model@ == scale::<V>(s.model(), v.model@),
    {
        let ghost model = scale::<V>(s.model(), v.model@);
        RuntimeVec4 {
            x: s.mul(&v.x), y: s.mul(&v.y),
            z: s.mul(&v.z), w: s.mul(&v.w),
            model: Ghost(model),
        }
    }

    pub fn dot_exec(&self, rhs: &Self) -> (out: R)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model() == dot::<V>(self.model@, rhs.model@),
    {
        self.x.mul(&rhs.x).add(&self.y.mul(&rhs.y))
            .add(&self.z.mul(&rhs.z)).add(&self.w.mul(&rhs.w))
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
        Self::scale_exec(&one_minus_t, self).add_exec(&Self::scale_exec(t, other))
    }
}

} //  verus!
