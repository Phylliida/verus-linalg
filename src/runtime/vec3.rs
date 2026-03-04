use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use crate::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use crate::vec3::ops::{scale, dot, norm_sq, lerp, cross, triple, cwise_min, cwise_max};
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// RuntimeVec3
// ---------------------------------------------------------------------------

pub struct RuntimeVec3 {
    pub x: RuntimeRational,
    pub y: RuntimeRational,
    pub z: RuntimeRational,
    pub model: Ghost<Vec3<RationalModel>>,
}

impl View for RuntimeVec3 {
    type V = Vec3<RationalModel>;

    open spec fn view(&self) -> Vec3<RationalModel> {
        self.model@
    }
}

impl RuntimeVec3 {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.z.wf_spec()
        &&& self.x@ == self@.x
        &&& self.y@ == self@.y
        &&& self.z@ == self@.z
    }

    pub fn new(x: RuntimeRational, y: RuntimeRational, z: RuntimeRational) -> (out: Self)
        requires
            x.wf_spec(),
            y.wf_spec(),
            z.wf_spec(),
        ensures
            out.wf_spec(),
            out@.x == x@,
            out@.y == y@,
            out@.z == z@,
    {
        let ghost model = Vec3 { x: x@, y: y@, z: z@ };
        RuntimeVec3 { x, y, z, model: Ghost(model) }
    }

    pub fn from_ints(x: i64, y: i64, z: i64) -> (out: Self)
        ensures
            out.wf_spec(),
    {
        let rx = RuntimeRational::from_int(x);
        let ry = RuntimeRational::from_int(y);
        let rz = RuntimeRational::from_int(z);
        Self::new(rx, ry, rz)
    }

    // -----------------------------------------------------------------------
    // Algebraic operations
    // -----------------------------------------------------------------------

    /// Vector addition
    pub fn add_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.add(rhs@),
    {
        let x = self.x.add(&rhs.x);
        let y = self.y.add(&rhs.y);
        let z = self.z.add(&rhs.z);
        let ghost model = self@.add(rhs@);
        RuntimeVec3 { x, y, z, model: Ghost(model) }
    }

    /// Vector subtraction
    pub fn sub_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.sub(rhs@),
    {
        let x = self.x.sub(&rhs.x);
        let y = self.y.sub(&rhs.y);
        let z = self.z.sub(&rhs.z);
        let ghost model = self@.sub(rhs@);
        RuntimeVec3 { x, y, z, model: Ghost(model) }
    }

    /// Vector negation
    pub fn neg_exec(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.neg(),
    {
        let x = self.x.neg();
        let y = self.y.neg();
        let z = self.z.neg();
        let ghost model = self@.neg();
        RuntimeVec3 { x, y, z, model: Ghost(model) }
    }

    /// Zero vector
    pub fn zero_exec() -> (out: Self)
        ensures
            out.wf_spec(),
            out@ == <Vec3<RationalModel> as AdditiveCommutativeMonoid>::zero(),
    {
        let x = RuntimeRational::from_int(0);
        let y = RuntimeRational::from_int(0);
        let z = RuntimeRational::from_int(0);
        let ghost model: Vec3<RationalModel> = <Vec3<RationalModel> as AdditiveCommutativeMonoid>::zero();
        RuntimeVec3 { x, y, z, model: Ghost(model) }
    }

    // -----------------------------------------------------------------------
    // Ops
    // -----------------------------------------------------------------------

    /// Scalar multiplication: s * v
    pub fn scale_exec(s: &RuntimeRational, v: &Self) -> (out: Self)
        requires
            s.wf_spec(),
            v.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == scale::<RationalModel>(s@, v@),
    {
        let x = s.mul(&v.x);
        let y = s.mul(&v.y);
        let z = s.mul(&v.z);
        let ghost model = scale::<RationalModel>(s@, v@);
        RuntimeVec3 { x, y, z, model: Ghost(model) }
    }

    /// Dot product: a · b
    pub fn dot_exec(&self, rhs: &Self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == dot::<RationalModel>(self@, rhs@),
    {
        let t1 = self.x.mul(&rhs.x);
        let t2 = self.y.mul(&rhs.y);
        let t3 = self.z.mul(&rhs.z);
        let s12 = t1.add(&t2);
        s12.add(&t3)
    }

    /// Squared norm: ||v||²
    pub fn norm_sq_exec(&self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == norm_sq::<RationalModel>(self@),
    {
        self.dot_exec(self)
    }

    /// Cross product: a × b
    pub fn cross_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == cross::<RationalModel>(self@, rhs@),
    {
        // x = a.y * b.z - a.z * b.y
        let t1 = self.y.mul(&rhs.z);
        let t2 = self.z.mul(&rhs.y);
        let cx = t1.sub(&t2);

        // y = a.z * b.x - a.x * b.z
        let t3 = self.z.mul(&rhs.x);
        let t4 = self.x.mul(&rhs.z);
        let cy = t3.sub(&t4);

        // z = a.x * b.y - a.y * b.x
        let t5 = self.x.mul(&rhs.y);
        let t6 = self.y.mul(&rhs.x);
        let cz = t5.sub(&t6);

        let ghost model = cross::<RationalModel>(self@, rhs@);
        RuntimeVec3 { x: cx, y: cy, z: cz, model: Ghost(model) }
    }

    /// Scalar triple product: a · (b × c)
    pub fn triple_exec(&self, b: &Self, c: &Self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
            b.wf_spec(),
            c.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == triple::<RationalModel>(self@, b@, c@),
    {
        let bc = b.cross_exec(c);
        self.dot_exec(&bc)
    }

    /// Linear interpolation: (1-t)*a + t*b
    pub fn lerp_exec(&self, other: &Self, t: &RuntimeRational) -> (out: Self)
        requires
            self.wf_spec(),
            other.wf_spec(),
            t.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == lerp::<RationalModel>(self@, other@, t@),
    {
        let one = RuntimeRational::from_int(1);
        let one_minus_t = one.sub(t);
        let sa = Self::scale_exec(&one_minus_t, self);
        let sb = Self::scale_exec(t, other);
        sa.add_exec(&sb)
    }

    /// Component-wise minimum
    pub fn cwise_min_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == cwise_min::<RationalModel>(self@, rhs@),
    {
        let x = self.x.min(&rhs.x);
        let y = self.y.min(&rhs.y);
        let z = self.z.min(&rhs.z);
        let ghost model = cwise_min::<RationalModel>(self@, rhs@);
        RuntimeVec3 { x, y, z, model: Ghost(model) }
    }

    /// Component-wise maximum
    pub fn cwise_max_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == cwise_max::<RationalModel>(self@, rhs@),
    {
        let x = self.x.max(&rhs.x);
        let y = self.y.max(&rhs.y);
        let z = self.z.max(&rhs.z);
        let ghost model = cwise_max::<RationalModel>(self@, rhs@);
        RuntimeVec3 { x, y, z, model: Ghost(model) }
    }
}

} // verus!
