#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::vec2::RuntimeVec2;
#[cfg(verus_keep_ghost)]
use crate::mat2::Mat2x2;
#[cfg(verus_keep_ghost)]
use crate::mat2::ops::{identity, mat_vec_mul, transpose, det, mat_mul, adjugate};
#[cfg(verus_keep_ghost)]
use crate::vec2::Vec2;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

pub struct RuntimeMat2x2<R, V: Ring> where R: RuntimeRingOps<V> {
    pub row0: RuntimeVec2<R, V>,
    pub row1: RuntimeVec2<R, V>,
    pub model: Ghost<Mat2x2<V>>,
}

impl<R: RuntimeRingOps<V>, V: Ring> RuntimeMat2x2<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.row0.wf_spec()
        &&& self.row1.wf_spec()
        &&& self.row0.model@ == self.model@.row0
        &&& self.row1.model@ == self.model@.row1
    }

    pub fn new(row0: RuntimeVec2<R, V>, row1: RuntimeVec2<R, V>) -> (out: Self)
        requires row0.wf_spec(), row1.wf_spec(),
        ensures out.wf_spec(), out.model@.row0 == row0.model@, out.model@.row1 == row1.model@,
    {
        let ghost model = Mat2x2 { row0: row0.model@, row1: row1.model@ };
        RuntimeMat2x2 { row0, row1, model: Ghost(model) }
    }

    pub fn add(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.add(rhs.model@),
    {
        let ghost model = self.model@.add(rhs.model@);
        RuntimeMat2x2 { row0: self.row0.add(&rhs.row0), row1: self.row1.add(&rhs.row1), model: Ghost(model) }
    }

    pub fn sub(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.sub(rhs.model@),
    {
        let ghost model = self.model@.sub(rhs.model@);
        RuntimeMat2x2 { row0: self.row0.sub(&rhs.row0), row1: self.row1.sub(&rhs.row1), model: Ghost(model) }
    }

    pub fn neg(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == self.model@.neg(),
    {
        let ghost model = self.model@.neg();
        RuntimeMat2x2 { row0: self.row0.neg(), row1: self.row1.neg(), model: Ghost(model) }
    }

    pub fn mat_vec_mul(&self, v: &RuntimeVec2<R, V>) -> (out: RuntimeVec2<R, V>)
        requires self.wf_spec(), v.wf_spec(),
        ensures out.wf_spec(), out.model@ == mat_vec_mul::<V>(self.model@, v.model@),
    {
        let x = self.row0.dot(v);
        let y = self.row1.dot(v);
        let ghost model = mat_vec_mul::<V>(self.model@, v.model@);
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    pub fn transpose(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == transpose::<V>(self.model@),
    {
        let row0 = RuntimeVec2::new(self.row0.x.copy(), self.row1.x.copy());
        let row1 = RuntimeVec2::new(self.row0.y.copy(), self.row1.y.copy());
        let ghost model = transpose::<V>(self.model@);
        RuntimeMat2x2 { row0, row1, model: Ghost(model) }
    }

    pub fn det(&self) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out@ == det::<V>(self.model@),
    {
        self.row0.x.mul(&self.row1.y).sub(&self.row0.y.mul(&self.row1.x))
    }

    pub fn mat_mul(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == mat_mul::<V>(self.model@, rhs.model@),
    {
        let bt = rhs.transpose();
        let row0 = RuntimeVec2::new(self.row0.dot(&bt.row0), self.row0.dot(&bt.row1));
        let row1 = RuntimeVec2::new(self.row1.dot(&bt.row0), self.row1.dot(&bt.row1));
        let ghost model = mat_mul::<V>(self.model@, rhs.model@);
        RuntimeMat2x2 { row0, row1, model: Ghost(model) }
    }

    pub fn adjugate(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == adjugate::<V>(self.model@),
    {
        let row0 = RuntimeVec2::new(self.row1.y.copy(), self.row0.y.neg());
        let row1 = RuntimeVec2::new(self.row1.x.neg(), self.row0.x.copy());
        let ghost model = adjugate::<V>(self.model@);
        RuntimeMat2x2 { row0, row1, model: Ghost(model) }
    }
}

} //  verus!
