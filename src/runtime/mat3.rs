use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::vec3::RuntimeVec3;
#[cfg(verus_keep_ghost)]
use super::copy_rational;
#[cfg(verus_keep_ghost)]
use crate::mat3::Mat3x3;
#[cfg(verus_keep_ghost)]
use crate::mat3::ops::{identity, mat_vec_mul, transpose, det, mat_mul, adjugate};
#[cfg(verus_keep_ghost)]
use crate::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use crate::vec3::ops::{dot, cross};
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  RuntimeMat3x3
//  ---------------------------------------------------------------------------

pub struct RuntimeMat3x3 {
    pub row0: RuntimeVec3,
    pub row1: RuntimeVec3,
    pub row2: RuntimeVec3,
    pub model: Ghost<Mat3x3<RationalModel>>,
}

impl View for RuntimeMat3x3 {
    type V = Mat3x3<RationalModel>;

    open spec fn view(&self) -> Mat3x3<RationalModel> {
        self.model@
    }
}

impl RuntimeMat3x3 {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.row0.wf_spec()
        &&& self.row1.wf_spec()
        &&& self.row2.wf_spec()
        &&& self.row0@ == self@.row0
        &&& self.row1@ == self@.row1
        &&& self.row2@ == self@.row2
    }

    pub fn new(row0: RuntimeVec3, row1: RuntimeVec3, row2: RuntimeVec3) -> (out: Self)
        requires
            row0.wf_spec(),
            row1.wf_spec(),
            row2.wf_spec(),
        ensures
            out.wf_spec(),
            out@.row0 == row0@,
            out@.row1 == row1@,
            out@.row2 == row2@,
    {
        let ghost model = Mat3x3 { row0: row0@, row1: row1@, row2: row2@ };
        RuntimeMat3x3 { row0, row1, row2, model: Ghost(model) }
    }

    //  -----------------------------------------------------------------------
    //  Ops
    //  -----------------------------------------------------------------------

    ///  Identity matrix
    pub fn identity_exec() -> (out: Self)
        ensures
            out.wf_spec(),
            out@ == identity::<RationalModel>(),
    {
        let row0 = RuntimeVec3::new(
            RuntimeRational::from_int(1), RuntimeRational::from_int(0), RuntimeRational::from_int(0),
        );
        let row1 = RuntimeVec3::new(
            RuntimeRational::from_int(0), RuntimeRational::from_int(1), RuntimeRational::from_int(0),
        );
        let row2 = RuntimeVec3::new(
            RuntimeRational::from_int(0), RuntimeRational::from_int(0), RuntimeRational::from_int(1),
        );
        let ghost model = identity::<RationalModel>();
        RuntimeMat3x3 { row0, row1, row2, model: Ghost(model) }
    }

    ///  Matrix-vector multiplication: M * v
    pub fn mat_vec_mul_exec(&self, v: &RuntimeVec3) -> (out: RuntimeVec3)
        requires
            self.wf_spec(),
            v.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == mat_vec_mul::<RationalModel>(self@, v@),
    {
        let x = self.row0.dot_exec(v);
        let y = self.row1.dot_exec(v);
        let z = self.row2.dot_exec(v);
        let ghost model = mat_vec_mul::<RationalModel>(self@, v@);
        RuntimeVec3 { x, y, z, model: Ghost(model) }
    }

    ///  Transpose
    pub fn transpose_exec(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == transpose::<RationalModel>(self@),
    {
        let row0 = RuntimeVec3::new(
            copy_rational(&self.row0.x), copy_rational(&self.row1.x), copy_rational(&self.row2.x),
        );
        let row1 = RuntimeVec3::new(
            copy_rational(&self.row0.y), copy_rational(&self.row1.y), copy_rational(&self.row2.y),
        );
        let row2 = RuntimeVec3::new(
            copy_rational(&self.row0.z), copy_rational(&self.row1.z), copy_rational(&self.row2.z),
        );
        let ghost model = transpose::<RationalModel>(self@);
        RuntimeMat3x3 { row0, row1, row2, model: Ghost(model) }
    }

    ///  Determinant: triple(row0, row1, row2)
    pub fn det_exec(&self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == det::<RationalModel>(self@),
    {
        self.row0.triple_exec(&self.row1, &self.row2)
    }

    ///  Matrix multiplication: A * B
    pub fn mat_mul_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == mat_mul::<RationalModel>(self@, rhs@),
    {
        let bt = rhs.transpose_exec();
        let r00 = self.row0.dot_exec(&bt.row0);
        let r01 = self.row0.dot_exec(&bt.row1);
        let r02 = self.row0.dot_exec(&bt.row2);
        let r10 = self.row1.dot_exec(&bt.row0);
        let r11 = self.row1.dot_exec(&bt.row1);
        let r12 = self.row1.dot_exec(&bt.row2);
        let r20 = self.row2.dot_exec(&bt.row0);
        let r21 = self.row2.dot_exec(&bt.row1);
        let r22 = self.row2.dot_exec(&bt.row2);
        let row0 = RuntimeVec3::new(r00, r01, r02);
        let row1 = RuntimeVec3::new(r10, r11, r12);
        let row2 = RuntimeVec3::new(r20, r21, r22);
        let ghost model = mat_mul::<RationalModel>(self@, rhs@);
        RuntimeMat3x3 { row0, row1, row2, model: Ghost(model) }
    }

    ///  Adjugate: transpose of cofactor matrix using cross products
    pub fn adjugate_exec(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == adjugate::<RationalModel>(self@),
    {
        let c12 = self.row1.cross_exec(&self.row2);
        let c20 = self.row2.cross_exec(&self.row0);
        let c01 = self.row0.cross_exec(&self.row1);
        //  Transpose of [c12, c20, c01]
        let row0 = RuntimeVec3::new(
            copy_rational(&c12.x), copy_rational(&c20.x), copy_rational(&c01.x),
        );
        let row1 = RuntimeVec3::new(
            copy_rational(&c12.y), copy_rational(&c20.y), copy_rational(&c01.y),
        );
        let row2 = RuntimeVec3::new(
            copy_rational(&c12.z), copy_rational(&c20.z), copy_rational(&c01.z),
        );
        let ghost model = adjugate::<RationalModel>(self@);
        RuntimeMat3x3 { row0, row1, row2, model: Ghost(model) }
    }
}

} //  verus!
