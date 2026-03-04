use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use crate::vec2::Vec2;
#[cfg(verus_keep_ghost)]
use crate::vec2::ops::{scale, dot, norm_sq, lerp, cwise_min, cwise_max};
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// RuntimeVec2
// ---------------------------------------------------------------------------

pub struct RuntimeVec2 {
    pub x: RuntimeRational,
    pub y: RuntimeRational,
    pub model: Ghost<Vec2<RationalModel>>,
}

impl View for RuntimeVec2 {
    type V = Vec2<RationalModel>;

    open spec fn view(&self) -> Vec2<RationalModel> {
        self.model@
    }
}

impl RuntimeVec2 {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.x@ == self@.x
        &&& self.y@ == self@.y
    }

    pub fn new(x: RuntimeRational, y: RuntimeRational) -> (out: Self)
        requires
            x.wf_spec(),
            y.wf_spec(),
        ensures
            out.wf_spec(),
            out@.x == x@,
            out@.y == y@,
    {
        let ghost model = Vec2 { x: x@, y: y@ };
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    pub fn from_ints(x: i64, y: i64) -> (out: Self)
        ensures
            out.wf_spec(),
    {
        let rx = RuntimeRational::from_int(x);
        let ry = RuntimeRational::from_int(y);
        Self::new(rx, ry)
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
        let ghost model = self@.add(rhs@);
        RuntimeVec2 { x, y, model: Ghost(model) }
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
        let ghost model = self@.sub(rhs@);
        RuntimeVec2 { x, y, model: Ghost(model) }
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
        let ghost model = self@.neg();
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    /// Zero vector
    pub fn zero_exec() -> (out: Self)
        ensures
            out.wf_spec(),
            out@ == <Vec2<RationalModel> as AdditiveCommutativeMonoid>::zero(),
    {
        let x = RuntimeRational::from_int(0);
        let y = RuntimeRational::from_int(0);
        let ghost model: Vec2<RationalModel> = <Vec2<RationalModel> as AdditiveCommutativeMonoid>::zero();
        RuntimeVec2 { x, y, model: Ghost(model) }
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
        let ghost model = scale::<RationalModel>(s@, v@);
        RuntimeVec2 { x, y, model: Ghost(model) }
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
        t1.add(&t2)
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
        let ghost model = cwise_min::<RationalModel>(self@, rhs@);
        RuntimeVec2 { x, y, model: Ghost(model) }
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
        let ghost model = cwise_max::<RationalModel>(self@, rhs@);
        RuntimeVec2 { x, y, model: Ghost(model) }
    }
}

} // verus!
