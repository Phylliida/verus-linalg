use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use crate::vec4::Vec4;
#[cfg(verus_keep_ghost)]
use crate::vec4::ops::{scale, dot, norm_sq, lerp, cwise_min, cwise_max};
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  RuntimeVec4
//  ---------------------------------------------------------------------------

pub struct RuntimeVec4 {
    pub x: RuntimeRational,
    pub y: RuntimeRational,
    pub z: RuntimeRational,
    pub w: RuntimeRational,
    pub model: Ghost<Vec4<RationalModel>>,
}

impl View for RuntimeVec4 {
    type V = Vec4<RationalModel>;

    open spec fn view(&self) -> Vec4<RationalModel> {
        self.model@
    }
}

impl RuntimeVec4 {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.z.wf_spec()
        &&& self.w.wf_spec()
        &&& self.x@ == self@.x
        &&& self.y@ == self@.y
        &&& self.z@ == self@.z
        &&& self.w@ == self@.w
    }

    pub fn new(x: RuntimeRational, y: RuntimeRational, z: RuntimeRational, w: RuntimeRational) -> (out: Self)
        requires
            x.wf_spec(),
            y.wf_spec(),
            z.wf_spec(),
            w.wf_spec(),
        ensures
            out.wf_spec(),
            out@.x == x@,
            out@.y == y@,
            out@.z == z@,
            out@.w == w@,
    {
        let ghost model = Vec4 { x: x@, y: y@, z: z@, w: w@ };
        RuntimeVec4 { x, y, z, w, model: Ghost(model) }
    }

    pub fn from_ints(x: i64, y: i64, z: i64, w: i64) -> (out: Self)
        ensures
            out.wf_spec(),
    {
        let rx = RuntimeRational::from_int(x);
        let ry = RuntimeRational::from_int(y);
        let rz = RuntimeRational::from_int(z);
        let rw = RuntimeRational::from_int(w);
        Self::new(rx, ry, rz, rw)
    }

    //  -----------------------------------------------------------------------
    //  Algebraic operations
    //  -----------------------------------------------------------------------

    ///  Vector addition
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
        let w = self.w.add(&rhs.w);
        let ghost model = self@.add(rhs@);
        RuntimeVec4 { x, y, z, w, model: Ghost(model) }
    }

    ///  Vector subtraction
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
        let w = self.w.sub(&rhs.w);
        let ghost model = self@.sub(rhs@);
        RuntimeVec4 { x, y, z, w, model: Ghost(model) }
    }

    ///  Vector negation
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
        let w = self.w.neg();
        let ghost model = self@.neg();
        RuntimeVec4 { x, y, z, w, model: Ghost(model) }
    }

    ///  Zero vector
    pub fn zero_exec() -> (out: Self)
        ensures
            out.wf_spec(),
            out@ == <Vec4<RationalModel> as AdditiveCommutativeMonoid>::zero(),
    {
        let x = RuntimeRational::from_int(0);
        let y = RuntimeRational::from_int(0);
        let z = RuntimeRational::from_int(0);
        let w = RuntimeRational::from_int(0);
        let ghost model: Vec4<RationalModel> = <Vec4<RationalModel> as AdditiveCommutativeMonoid>::zero();
        RuntimeVec4 { x, y, z, w, model: Ghost(model) }
    }

    //  -----------------------------------------------------------------------
    //  Ops
    //  -----------------------------------------------------------------------

    ///  Scalar multiplication: s * v
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
        let w = s.mul(&v.w);
        let ghost model = scale::<RationalModel>(s@, v@);
        RuntimeVec4 { x, y, z, w, model: Ghost(model) }
    }

    ///  Dot product: a · b
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
        let t4 = self.w.mul(&rhs.w);
        let s12 = t1.add(&t2);
        let s123 = s12.add(&t3);
        s123.add(&t4)
    }

    ///  Squared norm: ||v||²
    pub fn norm_sq_exec(&self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == norm_sq::<RationalModel>(self@),
    {
        self.dot_exec(self)
    }

    ///  Linear interpolation: (1-t)*a + t*b
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

    ///  Component-wise minimum
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
        let w = self.w.min(&rhs.w);
        let ghost model = cwise_min::<RationalModel>(self@, rhs@);
        RuntimeVec4 { x, y, z, w, model: Ghost(model) }
    }

    ///  Component-wise maximum
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
        let w = self.w.max(&rhs.w);
        let ghost model = cwise_max::<RationalModel>(self@, rhs@);
        RuntimeVec4 { x, y, z, w, model: Ghost(model) }
    }
}

} //  verus!
