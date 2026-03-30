#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::vec4::RuntimeVec4;
#[cfg(verus_keep_ghost)]
use crate::quat::Quat;
#[cfg(verus_keep_ghost)]
use crate::quat::ops::{scale, mul as quat_mul, conjugate, norm_sq, one, as_vec4};
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

pub struct RuntimeQuat<R, V: Ring> where R: RuntimeRingOps<V> {
    pub w: R,
    pub x: R,
    pub y: R,
    pub z: R,
    pub model: Ghost<Quat<V>>,
}

impl<R: RuntimeRingOps<V>, V: Ring> RuntimeQuat<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.w.wf_spec() &&& self.x.wf_spec()
        &&& self.y.wf_spec() &&& self.z.wf_spec()
        &&& self.w.model() == self.model@.w
        &&& self.x.model() == self.model@.x
        &&& self.y.model() == self.model@.y
        &&& self.z.model() == self.model@.z
    }

    pub fn new(w: R, x: R, y: R, z: R) -> (out: Self)
        requires w.wf_spec(), x.wf_spec(), y.wf_spec(), z.wf_spec(),
        ensures out.wf_spec(),
            out.model@.w == w.model(), out.model@.x == x.model(),
            out.model@.y == y.model(), out.model@.z == z.model(),
    {
        let ghost model = Quat { w: w.model(), x: x.model(), y: y.model(), z: z.model() };
        RuntimeQuat { w, x, y, z, model: Ghost(model) }
    }

    pub fn add(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.add(rhs.model@),
    {
        let ghost model = self.model@.add(rhs.model@);
        RuntimeQuat { w: self.w.add(&rhs.w), x: self.x.add(&rhs.x),
            y: self.y.add(&rhs.y), z: self.z.add(&rhs.z), model: Ghost(model) }
    }

    pub fn sub(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.sub(rhs.model@),
    {
        let ghost model = self.model@.sub(rhs.model@);
        RuntimeQuat { w: self.w.sub(&rhs.w), x: self.x.sub(&rhs.x),
            y: self.y.sub(&rhs.y), z: self.z.sub(&rhs.z), model: Ghost(model) }
    }

    pub fn neg(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.neg(),
    {
        let ghost model = self.model@.neg();
        RuntimeQuat { w: self.w.neg(), x: self.x.neg(),
            y: self.y.neg(), z: self.z.neg(), model: Ghost(model) }
    }

    pub fn scale(s: &R, q: &Self) -> (out: Self)
        requires s.wf_spec(), q.wf_spec(),
        ensures out.wf_spec(), out.model@ == scale::<V>(s.model(), q.model@),
    {
        let ghost model = scale::<V>(s.model(), q.model@);
        RuntimeQuat { w: s.mul(&q.w), x: s.mul(&q.x),
            y: s.mul(&q.y), z: s.mul(&q.z), model: Ghost(model) }
    }

    pub fn mul(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == quat_mul::<V>(self.model@, rhs.model@),
    {
        let rw = self.w.mul(&rhs.w).sub(&self.x.mul(&rhs.x))
            .sub(&self.y.mul(&rhs.y)).sub(&self.z.mul(&rhs.z));
        let rx = self.w.mul(&rhs.x).add(&self.x.mul(&rhs.w))
            .add(&self.y.mul(&rhs.z)).sub(&self.z.mul(&rhs.y));
        let ry = self.w.mul(&rhs.y).sub(&self.x.mul(&rhs.z))
            .add(&self.y.mul(&rhs.w)).add(&self.z.mul(&rhs.x));
        let rz = self.w.mul(&rhs.z).add(&self.x.mul(&rhs.y))
            .sub(&self.y.mul(&rhs.x)).add(&self.z.mul(&rhs.w));
        let ghost model = quat_mul::<V>(self.model@, rhs.model@);
        RuntimeQuat { w: rw, x: rx, y: ry, z: rz, model: Ghost(model) }
    }

    pub fn conjugate(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == conjugate::<V>(self.model@),
    {
        let ghost model = conjugate::<V>(self.model@);
        RuntimeQuat { w: self.w.copy(), x: self.x.neg(),
            y: self.y.neg(), z: self.z.neg(), model: Ghost(model) }
    }

    pub fn norm_sq(&self) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model() == norm_sq::<V>(self.model@),
    {
        self.w.mul(&self.w).add(&self.x.mul(&self.x))
            .add(&self.y.mul(&self.y)).add(&self.z.mul(&self.z))
    }

    pub fn as_vec4(&self) -> (out: RuntimeVec4<R, V>)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == as_vec4::<V>(self.model@),
    {
        let ghost model = as_vec4::<V>(self.model@);
        RuntimeVec4 { x: self.w.copy(), y: self.x.copy(),
            z: self.y.copy(), w: self.z.copy(), model: Ghost(model) }
    }
}

} //  verus!
