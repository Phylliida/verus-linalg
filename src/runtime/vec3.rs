#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use crate::vec3::ops::{scale, dot, norm_sq, lerp, cross, triple};
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

pub struct RuntimeVec3<R, V: Ring> where R: RuntimeRingOps<V> {
    pub x: R,
    pub y: R,
    pub z: R,
    pub model: Ghost<Vec3<V>>,
}

impl<R: RuntimeRingOps<V>, V: Ring> RuntimeVec3<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.z.wf_spec()
        &&& self.x.model() == self.model@.x
        &&& self.y.model() == self.model@.y
        &&& self.z.model() == self.model@.z
    }

    pub fn new(x: R, y: R, z: R) -> (out: Self)
        requires x.wf_spec(), y.wf_spec(), z.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == x.model(),
            out.model@.y == y.model(),
            out.model@.z == z.model(),
    {
        let ghost model = Vec3 { x: x.model(), y: y.model(), z: z.model() };
        RuntimeVec3 { x, y, z, model: Ghost(model) }
    }

    pub fn add_exec(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.add(rhs.model@),
    {
        let ghost model = self.model@.add(rhs.model@);
        RuntimeVec3 { x: self.x.add(&rhs.x), y: self.y.add(&rhs.y), z: self.z.add(&rhs.z), model: Ghost(model) }
    }

    pub fn sub_exec(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.sub(rhs.model@),
    {
        let ghost model = self.model@.sub(rhs.model@);
        RuntimeVec3 { x: self.x.sub(&rhs.x), y: self.y.sub(&rhs.y), z: self.z.sub(&rhs.z), model: Ghost(model) }
    }

    pub fn neg_exec(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.neg(),
    {
        let ghost model = self.model@.neg();
        RuntimeVec3 { x: self.x.neg(), y: self.y.neg(), z: self.z.neg(), model: Ghost(model) }
    }

    pub fn zero_exec(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == <Vec3<V> as AdditiveCommutativeMonoid>::zero(),
    {
        let ghost model: Vec3<V> = <Vec3<V> as AdditiveCommutativeMonoid>::zero();
        RuntimeVec3 { x: self.x.zero_like(), y: self.y.zero_like(), z: self.z.zero_like(), model: Ghost(model) }
    }

    pub fn scale_exec(s: &R, v: &Self) -> (out: Self)
        requires s.wf_spec(), v.wf_spec(),
        ensures out.wf_spec(), out.model@ == scale::<V>(s.model(), v.model@),
    {
        let ghost model = scale::<V>(s.model(), v.model@);
        RuntimeVec3 { x: s.mul(&v.x), y: s.mul(&v.y), z: s.mul(&v.z), model: Ghost(model) }
    }

    pub fn dot_exec(&self, rhs: &Self) -> (out: R)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model() == dot::<V>(self.model@, rhs.model@),
    {
        self.x.mul(&rhs.x).add(&self.y.mul(&rhs.y)).add(&self.z.mul(&rhs.z))
    }

    pub fn norm_sq_exec(&self) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model() == norm_sq::<V>(self.model@),
    {
        self.dot_exec(self)
    }

    pub fn cross_exec(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == cross::<V>(self.model@, rhs.model@),
    {
        let cx = self.y.mul(&rhs.z).sub(&self.z.mul(&rhs.y));
        let cy = self.z.mul(&rhs.x).sub(&self.x.mul(&rhs.z));
        let cz = self.x.mul(&rhs.y).sub(&self.y.mul(&rhs.x));
        let ghost model = cross::<V>(self.model@, rhs.model@);
        RuntimeVec3 { x: cx, y: cy, z: cz, model: Ghost(model) }
    }

    pub fn triple_exec(&self, b: &Self, c: &Self) -> (out: R)
        requires self.wf_spec(), b.wf_spec(), c.wf_spec(),
        ensures out.wf_spec(), out.model() == triple::<V>(self.model@, b.model@, c.model@),
    {
        self.dot_exec(&b.cross_exec(c))
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
