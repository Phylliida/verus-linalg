use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::vec3::RuntimeVec3;
#[cfg(verus_keep_ghost)]
use super::vec4::RuntimeVec4;
#[cfg(verus_keep_ghost)]
use super::copy_rational;
#[cfg(verus_keep_ghost)]
use crate::mat4::Mat4x4;
#[cfg(verus_keep_ghost)]
use crate::mat4::ops::{identity, mat_vec_mul, transpose, det, mat_mul, drop_x, drop_y, drop_z, drop_w};
#[cfg(verus_keep_ghost)]
use crate::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use crate::vec3::ops::triple;
#[cfg(verus_keep_ghost)]
use crate::vec4::Vec4;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

// ---------------------------------------------------------------------------
// RuntimeMat4x4
// ---------------------------------------------------------------------------

pub struct RuntimeMat4x4 {
    pub row0: RuntimeVec4,
    pub row1: RuntimeVec4,
    pub row2: RuntimeVec4,
    pub row3: RuntimeVec4,
    pub model: Ghost<Mat4x4<RationalModel>>,
}

impl View for RuntimeMat4x4 {
    type V = Mat4x4<RationalModel>;

    open spec fn view(&self) -> Mat4x4<RationalModel> {
        self.model@
    }
}

impl RuntimeMat4x4 {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.row0.wf_spec()
        &&& self.row1.wf_spec()
        &&& self.row2.wf_spec()
        &&& self.row3.wf_spec()
        &&& self.row0@ == self@.row0
        &&& self.row1@ == self@.row1
        &&& self.row2@ == self@.row2
        &&& self.row3@ == self@.row3
    }

    pub fn new(row0: RuntimeVec4, row1: RuntimeVec4, row2: RuntimeVec4, row3: RuntimeVec4) -> (out: Self)
        requires
            row0.wf_spec(),
            row1.wf_spec(),
            row2.wf_spec(),
            row3.wf_spec(),
        ensures
            out.wf_spec(),
            out@.row0 == row0@,
            out@.row1 == row1@,
            out@.row2 == row2@,
            out@.row3 == row3@,
    {
        let ghost model = Mat4x4 { row0: row0@, row1: row1@, row2: row2@, row3: row3@ };
        RuntimeMat4x4 { row0, row1, row2, row3, model: Ghost(model) }
    }

    // -----------------------------------------------------------------------
    // Ops
    // -----------------------------------------------------------------------

    /// Identity matrix
    pub fn identity_exec() -> (out: Self)
        ensures
            out.wf_spec(),
            out@ == identity::<RationalModel>(),
    {
        let row0 = RuntimeVec4::new(
            RuntimeRational::from_int(1), RuntimeRational::from_int(0),
            RuntimeRational::from_int(0), RuntimeRational::from_int(0),
        );
        let row1 = RuntimeVec4::new(
            RuntimeRational::from_int(0), RuntimeRational::from_int(1),
            RuntimeRational::from_int(0), RuntimeRational::from_int(0),
        );
        let row2 = RuntimeVec4::new(
            RuntimeRational::from_int(0), RuntimeRational::from_int(0),
            RuntimeRational::from_int(1), RuntimeRational::from_int(0),
        );
        let row3 = RuntimeVec4::new(
            RuntimeRational::from_int(0), RuntimeRational::from_int(0),
            RuntimeRational::from_int(0), RuntimeRational::from_int(1),
        );
        let ghost model = identity::<RationalModel>();
        RuntimeMat4x4 { row0, row1, row2, row3, model: Ghost(model) }
    }

    /// Matrix-vector multiplication: M * v
    pub fn mat_vec_mul_exec(&self, v: &RuntimeVec4) -> (out: RuntimeVec4)
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
        let w = self.row3.dot_exec(v);
        let ghost model = mat_vec_mul::<RationalModel>(self@, v@);
        RuntimeVec4 { x, y, z, w, model: Ghost(model) }
    }

    /// Transpose
    pub fn transpose_exec(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == transpose::<RationalModel>(self@),
    {
        let row0 = RuntimeVec4::new(
            copy_rational(&self.row0.x), copy_rational(&self.row1.x),
            copy_rational(&self.row2.x), copy_rational(&self.row3.x),
        );
        let row1 = RuntimeVec4::new(
            copy_rational(&self.row0.y), copy_rational(&self.row1.y),
            copy_rational(&self.row2.y), copy_rational(&self.row3.y),
        );
        let row2 = RuntimeVec4::new(
            copy_rational(&self.row0.z), copy_rational(&self.row1.z),
            copy_rational(&self.row2.z), copy_rational(&self.row3.z),
        );
        let row3 = RuntimeVec4::new(
            copy_rational(&self.row0.w), copy_rational(&self.row1.w),
            copy_rational(&self.row2.w), copy_rational(&self.row3.w),
        );
        let ghost model = transpose::<RationalModel>(self@);
        RuntimeMat4x4 { row0, row1, row2, row3, model: Ghost(model) }
    }

    /// Determinant via Laplace expansion along row 0
    pub fn det_exec(&self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == det::<RationalModel>(self@),
    {
        // Build RuntimeVec3 for drop_x of rows 1-3
        let dx1 = RuntimeVec3::new(copy_rational(&self.row1.y), copy_rational(&self.row1.z), copy_rational(&self.row1.w));
        let dx2 = RuntimeVec3::new(copy_rational(&self.row2.y), copy_rational(&self.row2.z), copy_rational(&self.row2.w));
        let dx3 = RuntimeVec3::new(copy_rational(&self.row3.y), copy_rational(&self.row3.z), copy_rational(&self.row3.w));
        let tx = dx1.triple_exec(&dx2, &dx3);

        // Build RuntimeVec3 for drop_y of rows 1-3
        let dy1 = RuntimeVec3::new(copy_rational(&self.row1.x), copy_rational(&self.row1.z), copy_rational(&self.row1.w));
        let dy2 = RuntimeVec3::new(copy_rational(&self.row2.x), copy_rational(&self.row2.z), copy_rational(&self.row2.w));
        let dy3 = RuntimeVec3::new(copy_rational(&self.row3.x), copy_rational(&self.row3.z), copy_rational(&self.row3.w));
        let ty = dy1.triple_exec(&dy2, &dy3);

        // Build RuntimeVec3 for drop_z of rows 1-3
        let dz1 = RuntimeVec3::new(copy_rational(&self.row1.x), copy_rational(&self.row1.y), copy_rational(&self.row1.w));
        let dz2 = RuntimeVec3::new(copy_rational(&self.row2.x), copy_rational(&self.row2.y), copy_rational(&self.row2.w));
        let dz3 = RuntimeVec3::new(copy_rational(&self.row3.x), copy_rational(&self.row3.y), copy_rational(&self.row3.w));
        let tz = dz1.triple_exec(&dz2, &dz3);

        // Build RuntimeVec3 for drop_w of rows 1-3
        let dw1 = RuntimeVec3::new(copy_rational(&self.row1.x), copy_rational(&self.row1.y), copy_rational(&self.row1.z));
        let dw2 = RuntimeVec3::new(copy_rational(&self.row2.x), copy_rational(&self.row2.y), copy_rational(&self.row2.z));
        let dw3 = RuntimeVec3::new(copy_rational(&self.row3.x), copy_rational(&self.row3.y), copy_rational(&self.row3.z));
        let tw = dw1.triple_exec(&dw2, &dw3);

        // det = r0.x*tx - r0.y*ty + r0.z*tz - r0.w*tw
        let c0 = copy_rational(&self.row0.x).mul(&tx);
        let c1 = copy_rational(&self.row0.y).mul(&ty);
        let c2 = copy_rational(&self.row0.z).mul(&tz);
        let c3 = copy_rational(&self.row0.w).mul(&tw);
        c0.sub(&c1).add(&c2).sub(&c3)
    }

    /// Matrix multiplication: A * B
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
        let r03 = self.row0.dot_exec(&bt.row3);
        let r10 = self.row1.dot_exec(&bt.row0);
        let r11 = self.row1.dot_exec(&bt.row1);
        let r12 = self.row1.dot_exec(&bt.row2);
        let r13 = self.row1.dot_exec(&bt.row3);
        let r20 = self.row2.dot_exec(&bt.row0);
        let r21 = self.row2.dot_exec(&bt.row1);
        let r22 = self.row2.dot_exec(&bt.row2);
        let r23 = self.row2.dot_exec(&bt.row3);
        let r30 = self.row3.dot_exec(&bt.row0);
        let r31 = self.row3.dot_exec(&bt.row1);
        let r32 = self.row3.dot_exec(&bt.row2);
        let r33 = self.row3.dot_exec(&bt.row3);
        let row0 = RuntimeVec4::new(r00, r01, r02, r03);
        let row1 = RuntimeVec4::new(r10, r11, r12, r13);
        let row2 = RuntimeVec4::new(r20, r21, r22, r23);
        let row3 = RuntimeVec4::new(r30, r31, r32, r33);
        let ghost model = mat_mul::<RationalModel>(self@, rhs@);
        RuntimeMat4x4 { row0, row1, row2, row3, model: Ghost(model) }
    }
}

} // verus!
