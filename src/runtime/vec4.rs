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
        &&& self.x@ == self.model@.x
        &&& self.y@ == self.model@.y
        &&& self.z@ == self.model@.z
        &&& self.w@ == self.model@.w
    }

    pub fn new(x: R, y: R, z: R, w: R) -> (out: Self)
        requires x.wf_spec(), y.wf_spec(), z.wf_spec(), w.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == x@,
            out.model@.y == y@,
            out.model@.z == z@,
            out.model@.w == w@,
    {
        let ghost model = Vec4 { x: x@, y: y@, z: z@, w: w@ };
        RuntimeVec4 { x, y, z, w, model: Ghost(model) }
    }

    pub fn add(&self, rhs: &Self) -> (out: Self)
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

    pub fn sub(&self, rhs: &Self) -> (out: Self)
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

    pub fn neg(&self) -> (out: Self)
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

    pub fn scale(s: &R, v: &Self) -> (out: Self)
        requires s.wf_spec(), v.wf_spec(),
        ensures out.wf_spec(), out.model@ == scale::<V>(s@, v.model@),
    {
        let ghost model = scale::<V>(s@, v.model@);
        RuntimeVec4 {
            x: s.mul(&v.x), y: s.mul(&v.y),
            z: s.mul(&v.z), w: s.mul(&v.w),
            model: Ghost(model),
        }
    }

    pub fn dot(&self, rhs: &Self) -> (out: R)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out@ == dot::<V>(self.model@, rhs.model@),
    {
        self.x.mul(&rhs.x).add(&self.y.mul(&rhs.y))
            .add(&self.z.mul(&rhs.z)).add(&self.w.mul(&rhs.w))
    }

    pub fn norm_sq(&self) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out@ == norm_sq::<V>(self.model@),
    {
        self.dot(self)
    }

    pub fn lerp(&self, other: &Self, t: &R) -> (out: Self)
        requires self.wf_spec(), other.wf_spec(), t.wf_spec(),
        ensures out.wf_spec(), out.model@ == lerp::<V>(self.model@, other.model@, t@),
    {
        let one = t.one_like();
        let one_minus_t = one.sub(t);
        Self::scale(&one_minus_t, self).add(&Self::scale(t, other))
    }
}

} //  verus!
