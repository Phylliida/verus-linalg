use verus_rational::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use super::RationalModel;
#[cfg(verus_keep_ghost)]
use super::vec4::RuntimeVec4;
#[cfg(verus_keep_ghost)]
use super::copy_rational;
#[cfg(verus_keep_ghost)]
use crate::quat::Quat;
#[cfg(verus_keep_ghost)]
use crate::quat::ops::{scale, mul as quat_mul, conjugate, norm_sq, one, as_vec4};
#[cfg(verus_keep_ghost)]
use crate::vec4::Vec4;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::*;

#[cfg(verus_keep_ghost)]
verus! {

//  ---------------------------------------------------------------------------
//  RuntimeQuat
//  ---------------------------------------------------------------------------

pub struct RuntimeQuat {
    pub w: RuntimeRational,
    pub x: RuntimeRational,
    pub y: RuntimeRational,
    pub z: RuntimeRational,
    pub model: Ghost<Quat<RationalModel>>,
}

impl View for RuntimeQuat {
    type V = Quat<RationalModel>;

    open spec fn view(&self) -> Quat<RationalModel> {
        self.model@
    }
}

impl RuntimeQuat {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.w.wf_spec()
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.z.wf_spec()
        &&& self.w@ == self@.w
        &&& self.x@ == self@.x
        &&& self.y@ == self@.y
        &&& self.z@ == self@.z
    }

    pub fn new(w: RuntimeRational, x: RuntimeRational, y: RuntimeRational, z: RuntimeRational) -> (out: Self)
        requires
            w.wf_spec(),
            x.wf_spec(),
            y.wf_spec(),
            z.wf_spec(),
        ensures
            out.wf_spec(),
            out@.w == w@,
            out@.x == x@,
            out@.y == y@,
            out@.z == z@,
    {
        let ghost model = Quat { w: w@, x: x@, y: y@, z: z@ };
        RuntimeQuat { w, x, y, z, model: Ghost(model) }
    }

    pub fn from_ints(w: i64, x: i64, y: i64, z: i64) -> (out: Self)
        ensures
            out.wf_spec(),
    {
        let rw = RuntimeRational::from_int(w);
        let rx = RuntimeRational::from_int(x);
        let ry = RuntimeRational::from_int(y);
        let rz = RuntimeRational::from_int(z);
        Self::new(rw, rx, ry, rz)
    }

    //  -----------------------------------------------------------------------
    //  Algebraic operations
    //  -----------------------------------------------------------------------

    ///  Quaternion addition
    pub fn add_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.add(rhs@),
    {
        let w = self.w.add(&rhs.w);
        let x = self.x.add(&rhs.x);
        let y = self.y.add(&rhs.y);
        let z = self.z.add(&rhs.z);
        let ghost model = self@.add(rhs@);
        RuntimeQuat { w, x, y, z, model: Ghost(model) }
    }

    ///  Quaternion subtraction
    pub fn sub_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.sub(rhs@),
    {
        let w = self.w.sub(&rhs.w);
        let x = self.x.sub(&rhs.x);
        let y = self.y.sub(&rhs.y);
        let z = self.z.sub(&rhs.z);
        let ghost model = self@.sub(rhs@);
        RuntimeQuat { w, x, y, z, model: Ghost(model) }
    }

    ///  Quaternion negation
    pub fn neg_exec(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == self@.neg(),
    {
        let w = self.w.neg();
        let x = self.x.neg();
        let y = self.y.neg();
        let z = self.z.neg();
        let ghost model = self@.neg();
        RuntimeQuat { w, x, y, z, model: Ghost(model) }
    }

    ///  Zero quaternion
    pub fn zero_exec() -> (out: Self)
        ensures
            out.wf_spec(),
            out@ == <Quat<RationalModel> as AdditiveCommutativeMonoid>::zero(),
    {
        let w = RuntimeRational::from_int(0);
        let x = RuntimeRational::from_int(0);
        let y = RuntimeRational::from_int(0);
        let z = RuntimeRational::from_int(0);
        let ghost model: Quat<RationalModel> = <Quat<RationalModel> as AdditiveCommutativeMonoid>::zero();
        RuntimeQuat { w, x, y, z, model: Ghost(model) }
    }

    ///  Unit quaternion (1, 0, 0, 0)
    pub fn one_exec() -> (out: Self)
        ensures
            out.wf_spec(),
            out@ == one::<RationalModel>(),
    {
        let w = RuntimeRational::from_int(1);
        let x = RuntimeRational::from_int(0);
        let y = RuntimeRational::from_int(0);
        let z = RuntimeRational::from_int(0);
        let ghost model = one::<RationalModel>();
        RuntimeQuat { w, x, y, z, model: Ghost(model) }
    }

    //  -----------------------------------------------------------------------
    //  Ops
    //  -----------------------------------------------------------------------

    ///  Scalar multiplication: s * q
    pub fn scale_exec(s: &RuntimeRational, q: &Self) -> (out: Self)
        requires
            s.wf_spec(),
            q.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == scale::<RationalModel>(s@, q@),
    {
        let w = s.mul(&q.w);
        let x = s.mul(&q.x);
        let y = s.mul(&q.y);
        let z = s.mul(&q.z);
        let ghost model = scale::<RationalModel>(s@, q@);
        RuntimeQuat { w, x, y, z, model: Ghost(model) }
    }

    ///  Hamilton product: a * b
    pub fn mul_exec(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == quat_mul::<RationalModel>(self@, rhs@),
    {
        //  w = aw*bw - ax*bx - ay*by - az*bz
        let ww = self.w.mul(&rhs.w);
        let xx = self.x.mul(&rhs.x);
        let yy = self.y.mul(&rhs.y);
        let zz = self.z.mul(&rhs.z);
        let rw = ww.sub(&xx).sub(&yy).sub(&zz);

        //  x = aw*bx + ax*bw + ay*bz - az*by
        let wx = self.w.mul(&rhs.x);
        let xw = self.x.mul(&rhs.w);
        let yz = self.y.mul(&rhs.z);
        let zy = self.z.mul(&rhs.y);
        let rx = wx.add(&xw).add(&yz).sub(&zy);

        //  y = aw*by - ax*bz + ay*bw + az*bx
        let wy = self.w.mul(&rhs.y);
        let xz = self.x.mul(&rhs.z);
        let yw = self.y.mul(&rhs.w);
        let zx = self.z.mul(&rhs.x);
        let ry = wy.sub(&xz).add(&yw).add(&zx);

        //  z = aw*bz + ax*by - ay*bx + az*bw
        let wz = self.w.mul(&rhs.z);
        let xy = self.x.mul(&rhs.y);
        let yx = self.y.mul(&rhs.x);
        let zw = self.z.mul(&rhs.w);
        let rz = wz.add(&xy).sub(&yx).add(&zw);

        let ghost model = quat_mul::<RationalModel>(self@, rhs@);
        RuntimeQuat { w: rw, x: rx, y: ry, z: rz, model: Ghost(model) }
    }

    ///  Conjugate: (w, -x, -y, -z)
    pub fn conjugate_exec(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == conjugate::<RationalModel>(self@),
    {
        let w = copy_rational(&self.w);
        let x = self.x.neg();
        let y = self.y.neg();
        let z = self.z.neg();
        let ghost model = conjugate::<RationalModel>(self@);
        RuntimeQuat { w, x, y, z, model: Ghost(model) }
    }

    ///  Squared norm: w² + x² + y² + z²
    pub fn norm_sq_exec(&self) -> (out: RuntimeRational)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == norm_sq::<RationalModel>(self@),
    {
        let ww = self.w.mul(&self.w);
        let xx = self.x.mul(&self.x);
        let yy = self.y.mul(&self.y);
        let zz = self.z.mul(&self.z);
        let s1 = ww.add(&xx);
        let s2 = s1.add(&yy);
        s2.add(&zz)
    }

    ///  Convert to Vec4: (w, x, y, z)
    pub fn as_vec4_exec(&self) -> (out: RuntimeVec4)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@ == as_vec4::<RationalModel>(self@),
    {
        let x = copy_rational(&self.w);
        let y = copy_rational(&self.x);
        let z = copy_rational(&self.y);
        let w = copy_rational(&self.z);
        let ghost model = as_vec4::<RationalModel>(self@);
        RuntimeVec4 { x, y, z, w, model: Ghost(model) }
    }
}

} //  verus!
