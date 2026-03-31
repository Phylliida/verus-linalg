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
        &&& self.x@ == self.model@.x
        &&& self.y@ == self.model@.y
        &&& self.z@ == self.model@.z
    }

    pub fn new(x: R, y: R, z: R) -> (out: Self)
        requires x.wf_spec(), y.wf_spec(), z.wf_spec(),
        ensures
            out.wf_spec(),
            out.model@.x == x@,
            out.model@.y == y@,
            out.model@.z == z@,
    {
        let ghost model = Vec3 { x: x@, y: y@, z: z@ };
        RuntimeVec3 { x, y, z, model: Ghost(model) }
    }

    pub fn add(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.add(rhs.model@),
    {
        let ghost model = self.model@.add(rhs.model@);
        RuntimeVec3 { x: self.x.add(&rhs.x), y: self.y.add(&rhs.y), z: self.z.add(&rhs.z), model: Ghost(model) }
    }

    pub fn sub(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.sub(rhs.model@),
    {
        let ghost model = self.model@.sub(rhs.model@);
        RuntimeVec3 { x: self.x.sub(&rhs.x), y: self.y.sub(&rhs.y), z: self.z.sub(&rhs.z), model: Ghost(model) }
    }

    pub fn neg(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.neg(),
    {
        let ghost model = self.model@.neg();
        RuntimeVec3 { x: self.x.neg(), y: self.y.neg(), z: self.z.neg(), model: Ghost(model) }
    }

    pub fn zero(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == <Vec3<V> as AdditiveCommutativeMonoid>::zero(),
    {
        let ghost model: Vec3<V> = <Vec3<V> as AdditiveCommutativeMonoid>::zero();
        RuntimeVec3 { x: self.x.zero_like(), y: self.y.zero_like(), z: self.z.zero_like(), model: Ghost(model) }
    }

    pub fn scale(s: &R, v: &Self) -> (out: Self)
        requires s.wf_spec(), v.wf_spec(),
        ensures out.wf_spec(), out.model@ == scale::<V>(s@, v.model@),
    {
        let ghost model = scale::<V>(s@, v.model@);
        RuntimeVec3 { x: s.mul(&v.x), y: s.mul(&v.y), z: s.mul(&v.z), model: Ghost(model) }
    }

    pub fn dot(&self, rhs: &Self) -> (out: R)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out@ == dot::<V>(self.model@, rhs.model@),
    {
        self.x.mul(&rhs.x).add(&self.y.mul(&rhs.y)).add(&self.z.mul(&rhs.z))
    }

    pub fn norm_sq(&self) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out@ == norm_sq::<V>(self.model@),
    {
        self.dot(self)
    }

    pub fn cross(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == cross::<V>(self.model@, rhs.model@),
    {
        let cx = self.y.mul(&rhs.z).sub(&self.z.mul(&rhs.y));
        let cy = self.z.mul(&rhs.x).sub(&self.x.mul(&rhs.z));
        let cz = self.x.mul(&rhs.y).sub(&self.y.mul(&rhs.x));
        let ghost model = cross::<V>(self.model@, rhs.model@);
        RuntimeVec3 { x: cx, y: cy, z: cz, model: Ghost(model) }
    }

    pub fn triple(&self, b: &Self, c: &Self) -> (out: R)
        requires self.wf_spec(), b.wf_spec(), c.wf_spec(),
        ensures out.wf_spec(), out@ == triple::<V>(self.model@, b.model@, c.model@),
    {
        self.dot(&b.cross(c))
    }

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
        Self::scale(&one_minus_t, self).add(&Self::scale(t, other))
    }
}

} //  verus!
