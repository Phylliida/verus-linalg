use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::vec2::RuntimeVec2;
#[cfg(verus_keep_ghost)]
use super::copy_rational;
#[cfg(verus_keep_ghost)]
use crate::mat2::Mat2x2;
#[cfg(verus_keep_ghost)]
use crate::mat2::ops::{identity, mat_vec_mul, transpose, det, mat_mul, adjugate};
#[cfg(verus_keep_ghost)]
use crate::vec2::Vec2;
#[cfg(verus_keep_ghost)]
use crate::vec2::ops::dot;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  RuntimeMat2x2
//  ---------------------------------------------------------------------------

pub struct RuntimeMat2x2 {
    pub row0: RuntimeVec2,
    pub row1: RuntimeVec2,
    pub model: Ghost<Mat2x2<RationalModel>>,
}

impl View for RuntimeMat2x2 {
    type V = Mat2x2<RationalModel>;

    open spec fn view(&self) -> Mat2x2<RationalModel> {
        self.model@
    }
}

impl RuntimeMat2x2 {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.row0.wf_spec()
        &&& self.row1.wf_spec()
        &&& self.row0@ == self@.row0
        &&& self.row1@ == self@.row1
    }

    pub fn new(row0: RuntimeVec2, row1: RuntimeVec2) -> (out: Self)
        requires
            row0.wf_spec(),
            row1.wf_spec(),
        ensures
            out.wf_spec(),
            out@.row0 == row0@,
            out@.row1 == row1@,
    {
        let ghost model = Mat2x2 { row0: row0@, row1: row1@ };
        RuntimeMat2x2 { row0, row1, model: Ghost(model) }
    }

    //  -----------------------------------------------------------------------
    //  Algebraic operations
    //  -----------------------------------------------------------------------

    ///  Matrix addition
    pub fn add_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.add(rhs@),
    {
        let row0 = self.row0.add_exec(&rhs.row0);
        let row1 = self.row1.add_exec(&rhs.row1);
        let ghost model = self@.add(rhs@);
        RuntimeMat2x2 { row0, row1, model: Ghost(model) }
    }

    ///  Matrix subtraction
    pub fn sub_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.sub(rhs@),
    {
        let row0 = self.row0.sub_exec(&rhs.row0);
        let row1 = self.row1.sub_exec(&rhs.row1);
        let ghost model = self@.sub(rhs@);
        RuntimeMat2x2 { row0, row1, model: Ghost(model) }
    }

    ///  Matrix negation
    pub fn neg_exec(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.neg(),
    {
        let row0 = self.row0.neg_exec();
        let row1 = self.row1.neg_exec();
        let ghost model = self@.neg();
        RuntimeMat2x2 { row0, row1, model: Ghost(model) }
    }

    ///  Zero matrix
    pub fn zero_exec() -> (out: Self)
        ensures
            out.wf_spec(),
            out@ == <Mat2x2<RationalModel> as AdditiveCommutativeMonoid>::zero(),
    {
        let row0 = RuntimeVec2::zero_exec();
        let row1 = RuntimeVec2::zero_exec();
        let ghost model: Mat2x2<RationalModel> = <Mat2x2<RationalModel> as AdditiveCommutativeMonoid>::zero();
        RuntimeMat2x2 { row0, row1, model: Ghost(model) }
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
        let row0 = RuntimeVec2::new(RuntimeRational::from_int(1), RuntimeRational::from_int(0));
        let row1 = RuntimeVec2::new(RuntimeRational::from_int(0), RuntimeRational::from_int(1));
        let ghost model = identity::<RationalModel>();
        RuntimeMat2x2 { row0, row1, model: Ghost(model) }
    }

    ///  Matrix-vector multiplication: M * v
    pub fn mat_vec_mul_exec(&self, v: &RuntimeVec2) -> (out: RuntimeVec2)
        requires
            self.wf_spec(),
            v.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == mat_vec_mul::<RationalModel>(self@, v@),
    {
        let x = self.row0.dot_exec(v);
        let y = self.row1.dot_exec(v);
        let ghost model = mat_vec_mul::<RationalModel>(self@, v@);
        RuntimeVec2 { x, y, model: Ghost(model) }
    }

    ///  Transpose
    pub fn transpose_exec(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == transpose::<RationalModel>(self@),
    {
        //  transpose: row0 = (m00, m10), row1 = (m01, m11)
        let r0x = copy_rational(&self.row0.x);
        let r0y = copy_rational(&self.row1.x);
        let r1x = copy_rational(&self.row0.y);
        let r1y = copy_rational(&self.row1.y);
        let row0 = RuntimeVec2::new(r0x, r0y);
        let row1 = RuntimeVec2::new(r1x, r1y);
        let ghost model = transpose::<RationalModel>(self@);
        RuntimeMat2x2 { row0, row1, model: Ghost(model) }
    }

    ///  Determinant: m00*m11 - m01*m10
    pub fn det_exec(&self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == det::<RationalModel>(self@),
    {
        let t1 = self.row0.x.mul(&self.row1.y);
        let t2 = self.row0.y.mul(&self.row1.x);
        t1.sub(&t2)
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
        let r10 = self.row1.dot_exec(&bt.row0);
        let r11 = self.row1.dot_exec(&bt.row1);
        let row0 = RuntimeVec2::new(r00, r01);
        let row1 = RuntimeVec2::new(r10, r11);
        let ghost model = mat_mul::<RationalModel>(self@, rhs@);
        RuntimeMat2x2 { row0, row1, model: Ghost(model) }
    }

    ///  Adjugate: [[m11, -m01], [-m10, m00]]
    pub fn adjugate_exec(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == adjugate::<RationalModel>(self@),
    {
        let r0x = copy_rational(&self.row1.y);
        let r0y = self.row0.y.neg();
        let r1x = self.row1.x.neg();
        let r1y = copy_rational(&self.row0.x);
        let row0 = RuntimeVec2::new(r0x, r0y);
        let row1 = RuntimeVec2::new(r1x, r1y);
        let ghost model = adjugate::<RationalModel>(self@);
        RuntimeMat2x2 { row0, row1, model: Ghost(model) }
    }
}

} //  verus!
