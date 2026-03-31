#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::vec3::RuntimeVec3;
#[cfg(verus_keep_ghost)]
use crate::mat3::Mat3x3;
#[cfg(verus_keep_ghost)]
use crate::mat3::ops::{identity, mat_vec_mul, transpose, det, mat_mul, adjugate};
#[cfg(verus_keep_ghost)]
use crate::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

pub struct RuntimeMat3x3<R, V: Ring> where R: RuntimeRingOps<V> {
    pub row0: RuntimeVec3<R, V>,
    pub row1: RuntimeVec3<R, V>,
    pub row2: RuntimeVec3<R, V>,
    pub model: Ghost<Mat3x3<V>>,
}

impl<R: RuntimeRingOps<V>, V: Ring> RuntimeMat3x3<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.row0.wf_spec()
        &&& self.row1.wf_spec()
        &&& self.row2.wf_spec()
        &&& self.row0.model@ == self.model@.row0
        &&& self.row1.model@ == self.model@.row1
        &&& self.row2.model@ == self.model@.row2
    }

    pub fn new(row0: RuntimeVec3<R, V>, row1: RuntimeVec3<R, V>, row2: RuntimeVec3<R, V>) -> (out: Self)
        requires row0.wf_spec(), row1.wf_spec(), row2.wf_spec(),
        ensures out.wf_spec(),
            out.model@.row0 == row0.model@, out.model@.row1 == row1.model@, out.model@.row2 == row2.model@,
    {
        let ghost model = Mat3x3 { row0: row0.model@, row1: row1.model@, row2: row2.model@ };
        RuntimeMat3x3 { row0, row1, row2, model: Ghost(model) }
    }

    pub fn mat_vec_mul(&self, v: &RuntimeVec3<R, V>) -> (out: RuntimeVec3<R, V>)
        requires self.wf_spec(), v.wf_spec(),
        ensures out.wf_spec(), out.model@ == mat_vec_mul::<V>(self.model@, v.model@),
    {
        let ghost model = mat_vec_mul::<V>(self.model@, v.model@);
        RuntimeVec3 { x: self.row0.dot(v), y: self.row1.dot(v), z: self.row2.dot(v), model: Ghost(model) }
    }

    pub fn transpose(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == transpose::<V>(self.model@),
    {
        let row0 = RuntimeVec3::new(self.row0.x.copy(), self.row1.x.copy(), self.row2.x.copy());
        let row1 = RuntimeVec3::new(self.row0.y.copy(), self.row1.y.copy(), self.row2.y.copy());
        let row2 = RuntimeVec3::new(self.row0.z.copy(), self.row1.z.copy(), self.row2.z.copy());
        let ghost model = transpose::<V>(self.model@);
        RuntimeMat3x3 { row0, row1, row2, model: Ghost(model) }
    }

    pub fn det(&self) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out@ == det::<V>(self.model@),
    {
        self.row0.triple(&self.row1, &self.row2)
    }

    pub fn mat_mul(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == mat_mul::<V>(self.model@, rhs.model@),
    {
        let bt = rhs.transpose();
        let row0 = RuntimeVec3::new(self.row0.dot(&bt.row0), self.row0.dot(&bt.row1), self.row0.dot(&bt.row2));
        let row1 = RuntimeVec3::new(self.row1.dot(&bt.row0), self.row1.dot(&bt.row1), self.row1.dot(&bt.row2));
        let row2 = RuntimeVec3::new(self.row2.dot(&bt.row0), self.row2.dot(&bt.row1), self.row2.dot(&bt.row2));
        let ghost model = mat_mul::<V>(self.model@, rhs.model@);
        RuntimeMat3x3 { row0, row1, row2, model: Ghost(model) }
    }

    pub fn adjugate(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == adjugate::<V>(self.model@),
    {
        let c12 = self.row1.cross(&self.row2);
        let c20 = self.row2.cross(&self.row0);
        let c01 = self.row0.cross(&self.row1);
        let row0 = RuntimeVec3::new(c12.x.copy(), c20.x.copy(), c01.x.copy());
        let row1 = RuntimeVec3::new(c12.y.copy(), c20.y.copy(), c01.y.copy());
        let row2 = RuntimeVec3::new(c12.z.copy(), c20.z.copy(), c01.z.copy());
        let ghost model = adjugate::<V>(self.model@);
        RuntimeMat3x3 { row0, row1, row2, model: Ghost(model) }
    }
}

} //  verus!
