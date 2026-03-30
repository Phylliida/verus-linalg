#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::vec3::RuntimeVec3;
#[cfg(verus_keep_ghost)]
use super::vec4::RuntimeVec4;
#[cfg(verus_keep_ghost)]
use crate::mat4::Mat4x4;
#[cfg(verus_keep_ghost)]
use crate::mat4::ops::{mat_vec_mul, transpose, det, mat_mul};
#[cfg(verus_keep_ghost)]
use crate::mat4::adjugate::adjugate;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

pub struct RuntimeMat4x4<R, V: Ring> where R: RuntimeRingOps<V> {
    pub row0: RuntimeVec4<R, V>,
    pub row1: RuntimeVec4<R, V>,
    pub row2: RuntimeVec4<R, V>,
    pub row3: RuntimeVec4<R, V>,
    pub model: Ghost<Mat4x4<V>>,
}

impl<R: RuntimeRingOps<V>, V: Ring> RuntimeMat4x4<R, V> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.row0.wf_spec() &&& self.row1.wf_spec()
        &&& self.row2.wf_spec() &&& self.row3.wf_spec()
        &&& self.row0.model@ == self.model@.row0
        &&& self.row1.model@ == self.model@.row1
        &&& self.row2.model@ == self.model@.row2
        &&& self.row3.model@ == self.model@.row3
    }

    pub fn new(row0: RuntimeVec4<R, V>, row1: RuntimeVec4<R, V>,
               row2: RuntimeVec4<R, V>, row3: RuntimeVec4<R, V>) -> (out: Self)
        requires row0.wf_spec(), row1.wf_spec(), row2.wf_spec(), row3.wf_spec(),
        ensures out.wf_spec(),
    {
        let ghost model = Mat4x4 { row0: row0.model@, row1: row1.model@, row2: row2.model@, row3: row3.model@ };
        RuntimeMat4x4 { row0, row1, row2, row3, model: Ghost(model) }
    }

    pub fn mat_vec_mul(&self, v: &RuntimeVec4<R, V>) -> (out: RuntimeVec4<R, V>)
        requires self.wf_spec(), v.wf_spec(),
        ensures out.wf_spec(), out.model@ == mat_vec_mul::<V>(self.model@, v.model@),
    {
        let ghost model = mat_vec_mul::<V>(self.model@, v.model@);
        RuntimeVec4 {
            x: self.row0.dot(v), y: self.row1.dot(v),
            z: self.row2.dot(v), w: self.row3.dot(v),
            model: Ghost(model),
        }
    }

    pub fn transpose(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == transpose::<V>(self.model@),
    {
        let row0 = RuntimeVec4::new(self.row0.x.copy(), self.row1.x.copy(), self.row2.x.copy(), self.row3.x.copy());
        let row1 = RuntimeVec4::new(self.row0.y.copy(), self.row1.y.copy(), self.row2.y.copy(), self.row3.y.copy());
        let row2 = RuntimeVec4::new(self.row0.z.copy(), self.row1.z.copy(), self.row2.z.copy(), self.row3.z.copy());
        let row3 = RuntimeVec4::new(self.row0.w.copy(), self.row1.w.copy(), self.row2.w.copy(), self.row3.w.copy());
        let ghost model = transpose::<V>(self.model@);
        RuntimeMat4x4 { row0, row1, row2, row3, model: Ghost(model) }
    }

    fn drop3(a: &R, b: &R, c: &R) -> (out: RuntimeVec3<R, V>)
        requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
        ensures out.wf_spec(), out.model@.x == a.model(), out.model@.y == b.model(), out.model@.z == c.model(),
    {
        RuntimeVec3::new(a.copy(), b.copy(), c.copy())
    }

    pub fn det(&self) -> (out: R)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model() == det::<V>(self.model@),
    {
        let tx = Self::drop3(&self.row1.y, &self.row1.z, &self.row1.w)
            .triple(&Self::drop3(&self.row2.y, &self.row2.z, &self.row2.w),
                          &Self::drop3(&self.row3.y, &self.row3.z, &self.row3.w));
        let ty = Self::drop3(&self.row1.x, &self.row1.z, &self.row1.w)
            .triple(&Self::drop3(&self.row2.x, &self.row2.z, &self.row2.w),
                          &Self::drop3(&self.row3.x, &self.row3.z, &self.row3.w));
        let tz = Self::drop3(&self.row1.x, &self.row1.y, &self.row1.w)
            .triple(&Self::drop3(&self.row2.x, &self.row2.y, &self.row2.w),
                          &Self::drop3(&self.row3.x, &self.row3.y, &self.row3.w));
        let tw = Self::drop3(&self.row1.x, &self.row1.y, &self.row1.z)
            .triple(&Self::drop3(&self.row2.x, &self.row2.y, &self.row2.z),
                          &Self::drop3(&self.row3.x, &self.row3.y, &self.row3.z));
        self.row0.x.copy().mul(&tx).sub(&self.row0.y.copy().mul(&ty))
            .add(&self.row0.z.copy().mul(&tz)).sub(&self.row0.w.copy().mul(&tw))
    }

    pub fn mat_mul(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out.model@ == mat_mul::<V>(self.model@, rhs.model@),
    {
        let bt = rhs.transpose();
        let row0 = RuntimeVec4::new(self.row0.dot(&bt.row0), self.row0.dot(&bt.row1),
            self.row0.dot(&bt.row2), self.row0.dot(&bt.row3));
        let row1 = RuntimeVec4::new(self.row1.dot(&bt.row0), self.row1.dot(&bt.row1),
            self.row1.dot(&bt.row2), self.row1.dot(&bt.row3));
        let row2 = RuntimeVec4::new(self.row2.dot(&bt.row0), self.row2.dot(&bt.row1),
            self.row2.dot(&bt.row2), self.row2.dot(&bt.row3));
        let row3 = RuntimeVec4::new(self.row3.dot(&bt.row0), self.row3.dot(&bt.row1),
            self.row3.dot(&bt.row2), self.row3.dot(&bt.row3));
        let ghost model = mat_mul::<V>(self.model@, rhs.model@);
        RuntimeMat4x4 { row0, row1, row2, row3, model: Ghost(model) }
    }

    pub fn adjugate(&self) -> (out: Self)
        requires self.wf_spec(),
        ensures out.wf_spec(), out.model@ == adjugate::<V>(self.model@),
    {
        //  cofactor_vec(ri, rj, rk) components are ± triple of 3-component minors
        //  cv0 from rows 1,2,3
        let cv0x = Self::drop3(&self.row1.y, &self.row1.z, &self.row1.w).triple(
            &Self::drop3(&self.row2.y, &self.row2.z, &self.row2.w),
            &Self::drop3(&self.row3.y, &self.row3.z, &self.row3.w));
        let cv0y = Self::drop3(&self.row1.x, &self.row1.z, &self.row1.w).triple(
            &Self::drop3(&self.row2.x, &self.row2.z, &self.row2.w),
            &Self::drop3(&self.row3.x, &self.row3.z, &self.row3.w)).neg();
        let cv0z = Self::drop3(&self.row1.x, &self.row1.y, &self.row1.w).triple(
            &Self::drop3(&self.row2.x, &self.row2.y, &self.row2.w),
            &Self::drop3(&self.row3.x, &self.row3.y, &self.row3.w));
        let cv0w = Self::drop3(&self.row1.x, &self.row1.y, &self.row1.z).triple(
            &Self::drop3(&self.row2.x, &self.row2.y, &self.row2.z),
            &Self::drop3(&self.row3.x, &self.row3.y, &self.row3.z)).neg();

        //  cv1 from rows 0,2,3
        let cv1x = Self::drop3(&self.row0.y, &self.row0.z, &self.row0.w).triple(
            &Self::drop3(&self.row2.y, &self.row2.z, &self.row2.w),
            &Self::drop3(&self.row3.y, &self.row3.z, &self.row3.w));
        let cv1y = Self::drop3(&self.row0.x, &self.row0.z, &self.row0.w).triple(
            &Self::drop3(&self.row2.x, &self.row2.z, &self.row2.w),
            &Self::drop3(&self.row3.x, &self.row3.z, &self.row3.w)).neg();
        let cv1z = Self::drop3(&self.row0.x, &self.row0.y, &self.row0.w).triple(
            &Self::drop3(&self.row2.x, &self.row2.y, &self.row2.w),
            &Self::drop3(&self.row3.x, &self.row3.y, &self.row3.w));
        let cv1w = Self::drop3(&self.row0.x, &self.row0.y, &self.row0.z).triple(
            &Self::drop3(&self.row2.x, &self.row2.y, &self.row2.z),
            &Self::drop3(&self.row3.x, &self.row3.y, &self.row3.z)).neg();

        //  cv2 from rows 0,1,3
        let cv2x = Self::drop3(&self.row0.y, &self.row0.z, &self.row0.w).triple(
            &Self::drop3(&self.row1.y, &self.row1.z, &self.row1.w),
            &Self::drop3(&self.row3.y, &self.row3.z, &self.row3.w));
        let cv2y = Self::drop3(&self.row0.x, &self.row0.z, &self.row0.w).triple(
            &Self::drop3(&self.row1.x, &self.row1.z, &self.row1.w),
            &Self::drop3(&self.row3.x, &self.row3.z, &self.row3.w)).neg();
        let cv2z = Self::drop3(&self.row0.x, &self.row0.y, &self.row0.w).triple(
            &Self::drop3(&self.row1.x, &self.row1.y, &self.row1.w),
            &Self::drop3(&self.row3.x, &self.row3.y, &self.row3.w));
        let cv2w = Self::drop3(&self.row0.x, &self.row0.y, &self.row0.z).triple(
            &Self::drop3(&self.row1.x, &self.row1.y, &self.row1.z),
            &Self::drop3(&self.row3.x, &self.row3.y, &self.row3.z)).neg();

        //  cv3 from rows 0,1,2
        let cv3x = Self::drop3(&self.row0.y, &self.row0.z, &self.row0.w).triple(
            &Self::drop3(&self.row1.y, &self.row1.z, &self.row1.w),
            &Self::drop3(&self.row2.y, &self.row2.z, &self.row2.w));
        let cv3y = Self::drop3(&self.row0.x, &self.row0.z, &self.row0.w).triple(
            &Self::drop3(&self.row1.x, &self.row1.z, &self.row1.w),
            &Self::drop3(&self.row2.x, &self.row2.z, &self.row2.w)).neg();
        let cv3z = Self::drop3(&self.row0.x, &self.row0.y, &self.row0.w).triple(
            &Self::drop3(&self.row1.x, &self.row1.y, &self.row1.w),
            &Self::drop3(&self.row2.x, &self.row2.y, &self.row2.w));
        let cv3w = Self::drop3(&self.row0.x, &self.row0.y, &self.row0.z).triple(
            &Self::drop3(&self.row1.x, &self.row1.y, &self.row1.z),
            &Self::drop3(&self.row2.x, &self.row2.y, &self.row2.z)).neg();

        //  Transpose of [cv0, -cv1, cv2, -cv3]
        let row0 = RuntimeVec4::new(cv0x, cv1x.neg(), cv2x, cv3x.neg());
        let row1 = RuntimeVec4::new(cv0y, cv1y.neg(), cv2y, cv3y.neg());
        let row2 = RuntimeVec4::new(cv0z, cv1z.neg(), cv2z, cv3z.neg());
        let row3 = RuntimeVec4::new(cv0w, cv1w.neg(), cv2w, cv3w.neg());
        let ghost model = adjugate::<V>(self.model@);
        RuntimeMat4x4 { row0, row1, row2, row3, model: Ghost(model) }
    }
}

} //  verus!
