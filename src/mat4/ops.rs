use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use crate::vec3::Vec3;
use crate::vec3::ops::{triple, lemma_triple_congruence_first, lemma_triple_congruence_second, lemma_triple_congruence_third};
use crate::vec4::Vec4;
use crate::vec4::ops::{dot, scale};
use super::Mat4x4;

verus! {

// ---------------------------------------------------------------------------
// Spec functions
// ---------------------------------------------------------------------------

pub open spec fn identity<T: Ring>() -> Mat4x4<T> {
    Mat4x4 {
        row0: Vec4 { x: T::one(),  y: T::zero(), z: T::zero(), w: T::zero() },
        row1: Vec4 { x: T::zero(), y: T::one(),  z: T::zero(), w: T::zero() },
        row2: Vec4 { x: T::zero(), y: T::zero(), z: T::one(),  w: T::zero() },
        row3: Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: T::one()  },
    }
}

pub open spec fn mat_vec_mul<T: Ring>(m: Mat4x4<T>, v: Vec4<T>) -> Vec4<T> {
    Vec4 {
        x: dot(m.row0, v),
        y: dot(m.row1, v),
        z: dot(m.row2, v),
        w: dot(m.row3, v),
    }
}

pub open spec fn transpose<T: Ring>(m: Mat4x4<T>) -> Mat4x4<T> {
    Mat4x4 {
        row0: Vec4 { x: m.row0.x, y: m.row1.x, z: m.row2.x, w: m.row3.x },
        row1: Vec4 { x: m.row0.y, y: m.row1.y, z: m.row2.y, w: m.row3.y },
        row2: Vec4 { x: m.row0.z, y: m.row1.z, z: m.row2.z, w: m.row3.z },
        row3: Vec4 { x: m.row0.w, y: m.row1.w, z: m.row2.w, w: m.row3.w },
    }
}

pub open spec fn mat_mul<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>) -> Mat4x4<T> {
    let bt = transpose(b);
    Mat4x4 {
        row0: Vec4 {
            x: dot(a.row0, bt.row0),
            y: dot(a.row0, bt.row1),
            z: dot(a.row0, bt.row2),
            w: dot(a.row0, bt.row3),
        },
        row1: Vec4 {
            x: dot(a.row1, bt.row0),
            y: dot(a.row1, bt.row1),
            z: dot(a.row1, bt.row2),
            w: dot(a.row1, bt.row3),
        },
        row2: Vec4 {
            x: dot(a.row2, bt.row0),
            y: dot(a.row2, bt.row1),
            z: dot(a.row2, bt.row2),
            w: dot(a.row2, bt.row3),
        },
        row3: Vec4 {
            x: dot(a.row3, bt.row0),
            y: dot(a.row3, bt.row1),
            z: dot(a.row3, bt.row2),
            w: dot(a.row3, bt.row3),
        },
    }
}

/// Drop the x component, yielding (y, z, w)
pub open spec fn drop_x<T: Ring>(v: Vec4<T>) -> Vec3<T> {
    Vec3 { x: v.y, y: v.z, z: v.w }
}

/// Drop the y component, yielding (x, z, w)
pub open spec fn drop_y<T: Ring>(v: Vec4<T>) -> Vec3<T> {
    Vec3 { x: v.x, y: v.z, z: v.w }
}

/// Drop the z component, yielding (x, y, w)
pub open spec fn drop_z<T: Ring>(v: Vec4<T>) -> Vec3<T> {
    Vec3 { x: v.x, y: v.y, z: v.w }
}

/// Drop the w component, yielding (x, y, z)
pub open spec fn drop_w<T: Ring>(v: Vec4<T>) -> Vec3<T> {
    Vec3 { x: v.x, y: v.y, z: v.z }
}

/// 4×4 determinant via Laplace expansion along row 0:
/// det(m) = r0.x * triple(drop_x(r1), drop_x(r2), drop_x(r3))
///        - r0.y * triple(drop_y(r1), drop_y(r2), drop_y(r3))
///        + r0.z * triple(drop_z(r1), drop_z(r2), drop_z(r3))
///        - r0.w * triple(drop_w(r1), drop_w(r2), drop_w(r3))
pub open spec fn det<T: Ring>(m: Mat4x4<T>) -> T {
    let r0 = m.row0;
    let r1 = m.row1;
    let r2 = m.row2;
    let r3 = m.row3;
    r0.x.mul(triple(drop_x(r1), drop_x(r2), drop_x(r3)))
        .sub(r0.y.mul(triple(drop_y(r1), drop_y(r2), drop_y(r3))))
        .add(r0.z.mul(triple(drop_z(r1), drop_z(r2), drop_z(r3))))
        .sub(r0.w.mul(triple(drop_w(r1), drop_w(r2), drop_w(r3))))
}

// ---------------------------------------------------------------------------
// Transpose
// ---------------------------------------------------------------------------

/// transpose(transpose(m)) ≡ m  (structurally identical, just needs reflexivity)
pub proof fn lemma_transpose_involution<T: Ring>(m: Mat4x4<T>)
    ensures
        transpose(transpose(m)).row0.eqv(m.row0),
        transpose(transpose(m)).row1.eqv(m.row1),
        transpose(transpose(m)).row2.eqv(m.row2),
        transpose(transpose(m)).row3.eqv(m.row3),
{
    T::axiom_eqv_reflexive(m.row0.x);
    T::axiom_eqv_reflexive(m.row0.y);
    T::axiom_eqv_reflexive(m.row0.z);
    T::axiom_eqv_reflexive(m.row0.w);
    T::axiom_eqv_reflexive(m.row1.x);
    T::axiom_eqv_reflexive(m.row1.y);
    T::axiom_eqv_reflexive(m.row1.z);
    T::axiom_eqv_reflexive(m.row1.w);
    T::axiom_eqv_reflexive(m.row2.x);
    T::axiom_eqv_reflexive(m.row2.y);
    T::axiom_eqv_reflexive(m.row2.z);
    T::axiom_eqv_reflexive(m.row2.w);
    T::axiom_eqv_reflexive(m.row3.x);
    T::axiom_eqv_reflexive(m.row3.y);
    T::axiom_eqv_reflexive(m.row3.z);
    T::axiom_eqv_reflexive(m.row3.w);
}

// ---------------------------------------------------------------------------
// mat_vec_mul lemmas
// ---------------------------------------------------------------------------

/// mat_vec_mul(m, zero) ≡ zero
pub proof fn lemma_mat_vec_mul_zero<T: Ring>(m: Mat4x4<T>)
    ensures
        mat_vec_mul(m, Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: T::zero() })
            .eqv(Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: T::zero() }),
{
    let z = Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: T::zero() };
    crate::vec4::ops::lemma_dot_zero_right(m.row0);
    crate::vec4::ops::lemma_dot_zero_right(m.row1);
    crate::vec4::ops::lemma_dot_zero_right(m.row2);
    crate::vec4::ops::lemma_dot_zero_right(m.row3);
}

/// mat_vec_mul(m, a + b) ≡ mat_vec_mul(m, a) + mat_vec_mul(m, b)
pub proof fn lemma_mat_vec_mul_add<T: Ring>(m: Mat4x4<T>, a: Vec4<T>, b: Vec4<T>)
    ensures
        mat_vec_mul(m, a.add(b)).eqv(
            mat_vec_mul(m, a).add(mat_vec_mul(m, b))
        ),
{
    crate::vec4::ops::lemma_dot_distributes_right(m.row0, a, b);
    crate::vec4::ops::lemma_dot_distributes_right(m.row1, a, b);
    crate::vec4::ops::lemma_dot_distributes_right(m.row2, a, b);
    crate::vec4::ops::lemma_dot_distributes_right(m.row3, a, b);
}

/// mat_vec_mul(m, scale(s, v)) ≡ scale(s, mat_vec_mul(m, v))
pub proof fn lemma_mat_vec_mul_scale<T: Ring>(m: Mat4x4<T>, s: T, v: Vec4<T>)
    ensures
        mat_vec_mul(m, scale(s, v)).eqv(
            scale(s, mat_vec_mul(m, v))
        ),
{
    crate::vec4::ops::lemma_dot_scale_right(s, m.row0, v);
    crate::vec4::ops::lemma_dot_scale_right(s, m.row1, v);
    crate::vec4::ops::lemma_dot_scale_right(s, m.row2, v);
    crate::vec4::ops::lemma_dot_scale_right(s, m.row3, v);
}

// ---------------------------------------------------------------------------
// Basis dot lemmas (4D)
// ---------------------------------------------------------------------------

/// dot(e0, v) ≡ v.x
pub proof fn lemma_dot_e0<T: Ring>(v: Vec4<T>)
    ensures
        dot(Vec4::<T> { x: T::one(), y: T::zero(), z: T::zero(), w: T::zero() }, v).eqv(v.x),
{
    // dot(e0, v) = ((1*v.x + 0*v.y) + 0*v.z) + 0*v.w
    ring_lemmas::lemma_mul_one_left::<T>(v.x);
    ring_lemmas::lemma_mul_zero_left::<T>(v.y);
    ring_lemmas::lemma_mul_zero_left::<T>(v.z);
    ring_lemmas::lemma_mul_zero_left::<T>(v.w);

    // 1*v.x + 0*v.y ≡ v.x + 0 ≡ v.x
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().mul(v.x), v.x, T::zero().mul(v.y), T::zero(),
    );
    T::axiom_add_zero_right(v.x);
    T::axiom_eqv_transitive(
        T::one().mul(v.x).add(T::zero().mul(v.y)),
        v.x.add(T::zero()), v.x,
    );

    // (...) + 0*v.z ≡ v.x + 0 ≡ v.x
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().mul(v.x).add(T::zero().mul(v.y)), v.x,
        T::zero().mul(v.z), T::zero(),
    );
    T::axiom_add_zero_right(v.x);
    T::axiom_eqv_transitive(
        T::one().mul(v.x).add(T::zero().mul(v.y)).add(T::zero().mul(v.z)),
        v.x.add(T::zero()), v.x,
    );

    // (...) + 0*v.w ≡ v.x + 0 ≡ v.x
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().mul(v.x).add(T::zero().mul(v.y)).add(T::zero().mul(v.z)), v.x,
        T::zero().mul(v.w), T::zero(),
    );
    T::axiom_add_zero_right(v.x);
    T::axiom_eqv_transitive(
        dot(Vec4::<T> { x: T::one(), y: T::zero(), z: T::zero(), w: T::zero() }, v),
        v.x.add(T::zero()), v.x,
    );
}

/// dot(e1, v) ≡ v.y
pub proof fn lemma_dot_e1<T: Ring>(v: Vec4<T>)
    ensures
        dot(Vec4::<T> { x: T::zero(), y: T::one(), z: T::zero(), w: T::zero() }, v).eqv(v.y),
{
    ring_lemmas::lemma_mul_zero_left::<T>(v.x);
    ring_lemmas::lemma_mul_one_left::<T>(v.y);
    ring_lemmas::lemma_mul_zero_left::<T>(v.z);
    ring_lemmas::lemma_mul_zero_left::<T>(v.w);

    // 0*v.x + 1*v.y ≡ 0 + v.y ≡ v.y
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(v.x), T::zero(), T::one().mul(v.y), v.y,
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(v.y);
    T::axiom_eqv_transitive(
        T::zero().mul(v.x).add(T::one().mul(v.y)),
        T::zero().add(v.y), v.y,
    );

    // (...) + 0*v.z ≡ v.y + 0 ≡ v.y
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(v.x).add(T::one().mul(v.y)), v.y,
        T::zero().mul(v.z), T::zero(),
    );
    T::axiom_add_zero_right(v.y);
    T::axiom_eqv_transitive(
        T::zero().mul(v.x).add(T::one().mul(v.y)).add(T::zero().mul(v.z)),
        v.y.add(T::zero()), v.y,
    );

    // (...) + 0*v.w ≡ v.y + 0 ≡ v.y
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(v.x).add(T::one().mul(v.y)).add(T::zero().mul(v.z)), v.y,
        T::zero().mul(v.w), T::zero(),
    );
    T::axiom_add_zero_right(v.y);
    T::axiom_eqv_transitive(
        dot(Vec4::<T> { x: T::zero(), y: T::one(), z: T::zero(), w: T::zero() }, v),
        v.y.add(T::zero()), v.y,
    );
}

/// dot(e2, v) ≡ v.z
pub proof fn lemma_dot_e2<T: Ring>(v: Vec4<T>)
    ensures
        dot(Vec4::<T> { x: T::zero(), y: T::zero(), z: T::one(), w: T::zero() }, v).eqv(v.z),
{
    ring_lemmas::lemma_mul_zero_left::<T>(v.x);
    ring_lemmas::lemma_mul_zero_left::<T>(v.y);
    ring_lemmas::lemma_mul_one_left::<T>(v.z);
    ring_lemmas::lemma_mul_zero_left::<T>(v.w);

    // 0*v.x + 0*v.y ≡ 0 + 0 ≡ 0
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(v.x), T::zero(), T::zero().mul(v.y), T::zero(),
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
    T::axiom_eqv_transitive(
        T::zero().mul(v.x).add(T::zero().mul(v.y)),
        T::zero().add(T::zero()), T::zero(),
    );

    // 0 + 1*v.z ≡ 0 + v.z ≡ v.z
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(v.x).add(T::zero().mul(v.y)), T::zero(),
        T::one().mul(v.z), v.z,
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(v.z);
    T::axiom_eqv_transitive(
        T::zero().mul(v.x).add(T::zero().mul(v.y)).add(T::one().mul(v.z)),
        T::zero().add(v.z), v.z,
    );

    // (...) + 0*v.w ≡ v.z + 0 ≡ v.z
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(v.x).add(T::zero().mul(v.y)).add(T::one().mul(v.z)), v.z,
        T::zero().mul(v.w), T::zero(),
    );
    T::axiom_add_zero_right(v.z);
    T::axiom_eqv_transitive(
        dot(Vec4::<T> { x: T::zero(), y: T::zero(), z: T::one(), w: T::zero() }, v),
        v.z.add(T::zero()), v.z,
    );
}

/// dot(e3, v) ≡ v.w
pub proof fn lemma_dot_e3<T: Ring>(v: Vec4<T>)
    ensures
        dot(Vec4::<T> { x: T::zero(), y: T::zero(), z: T::zero(), w: T::one() }, v).eqv(v.w),
{
    ring_lemmas::lemma_mul_zero_left::<T>(v.x);
    ring_lemmas::lemma_mul_zero_left::<T>(v.y);
    ring_lemmas::lemma_mul_zero_left::<T>(v.z);
    ring_lemmas::lemma_mul_one_left::<T>(v.w);

    // 0*v.x + 0*v.y ≡ 0
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(v.x), T::zero(), T::zero().mul(v.y), T::zero(),
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
    T::axiom_eqv_transitive(
        T::zero().mul(v.x).add(T::zero().mul(v.y)),
        T::zero().add(T::zero()), T::zero(),
    );

    // 0 + 0*v.z ≡ 0
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(v.x).add(T::zero().mul(v.y)), T::zero(),
        T::zero().mul(v.z), T::zero(),
    );
    T::axiom_add_zero_right(T::zero());
    T::axiom_eqv_transitive(
        T::zero().mul(v.x).add(T::zero().mul(v.y)).add(T::zero().mul(v.z)),
        T::zero().add(T::zero()), T::zero(),
    );

    // 0 + 1*v.w ≡ 0 + v.w ≡ v.w
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(v.x).add(T::zero().mul(v.y)).add(T::zero().mul(v.z)), T::zero(),
        T::one().mul(v.w), v.w,
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(v.w);
    T::axiom_eqv_transitive(
        dot(Vec4::<T> { x: T::zero(), y: T::zero(), z: T::zero(), w: T::one() }, v),
        T::zero().add(v.w), v.w,
    );
}

/// dot(v, e0) ≡ v.x
pub proof fn lemma_dot_e0_right<T: Ring>(v: Vec4<T>)
    ensures
        dot(v, Vec4::<T> { x: T::one(), y: T::zero(), z: T::zero(), w: T::zero() }).eqv(v.x),
{
    let e0 = Vec4::<T> { x: T::one(), y: T::zero(), z: T::zero(), w: T::zero() };
    crate::vec4::ops::lemma_dot_commutative(v, e0);
    lemma_dot_e0(v);
    T::axiom_eqv_transitive(dot(v, e0), dot(e0, v), v.x);
}

/// dot(v, e1) ≡ v.y
pub proof fn lemma_dot_e1_right<T: Ring>(v: Vec4<T>)
    ensures
        dot(v, Vec4::<T> { x: T::zero(), y: T::one(), z: T::zero(), w: T::zero() }).eqv(v.y),
{
    let e1 = Vec4::<T> { x: T::zero(), y: T::one(), z: T::zero(), w: T::zero() };
    crate::vec4::ops::lemma_dot_commutative(v, e1);
    lemma_dot_e1(v);
    T::axiom_eqv_transitive(dot(v, e1), dot(e1, v), v.y);
}

/// dot(v, e2) ≡ v.z
pub proof fn lemma_dot_e2_right<T: Ring>(v: Vec4<T>)
    ensures
        dot(v, Vec4::<T> { x: T::zero(), y: T::zero(), z: T::one(), w: T::zero() }).eqv(v.z),
{
    let e2 = Vec4::<T> { x: T::zero(), y: T::zero(), z: T::one(), w: T::zero() };
    crate::vec4::ops::lemma_dot_commutative(v, e2);
    lemma_dot_e2(v);
    T::axiom_eqv_transitive(dot(v, e2), dot(e2, v), v.z);
}

/// dot(v, e3) ≡ v.w
pub proof fn lemma_dot_e3_right<T: Ring>(v: Vec4<T>)
    ensures
        dot(v, Vec4::<T> { x: T::zero(), y: T::zero(), z: T::zero(), w: T::one() }).eqv(v.w),
{
    let e3 = Vec4::<T> { x: T::zero(), y: T::zero(), z: T::zero(), w: T::one() };
    crate::vec4::ops::lemma_dot_commutative(v, e3);
    lemma_dot_e3(v);
    T::axiom_eqv_transitive(dot(v, e3), dot(e3, v), v.w);
}

// ---------------------------------------------------------------------------
// Identity matrix lemmas
// ---------------------------------------------------------------------------

/// mat_vec_mul(identity(), v) ≡ v
pub proof fn lemma_identity_mul_vec<T: Ring>(v: Vec4<T>)
    ensures
        mat_vec_mul(identity(), v).eqv(v),
{
    lemma_dot_e0(v);
    lemma_dot_e1(v);
    lemma_dot_e2(v);
    lemma_dot_e3(v);
}

/// mat_mul(identity(), m).row_i ≡ m.row_i
pub proof fn lemma_identity_mat_mul_left<T: Ring>(m: Mat4x4<T>)
    ensures
        mat_mul(identity(), m).row0.eqv(m.row0),
        mat_mul(identity(), m).row1.eqv(m.row1),
        mat_mul(identity(), m).row2.eqv(m.row2),
        mat_mul(identity(), m).row3.eqv(m.row3),
{
    let bt = transpose(m);
    // Row 0: dot(e0, bt.row_j) ≡ bt.row_j.x = m.row0.{x,y,z,w}
    lemma_dot_e0(bt.row0);
    lemma_dot_e0(bt.row1);
    lemma_dot_e0(bt.row2);
    lemma_dot_e0(bt.row3);
    // Row 1: dot(e1, bt.row_j) ≡ bt.row_j.y = m.row1.{x,y,z,w}
    lemma_dot_e1(bt.row0);
    lemma_dot_e1(bt.row1);
    lemma_dot_e1(bt.row2);
    lemma_dot_e1(bt.row3);
    // Row 2: dot(e2, bt.row_j) ≡ bt.row_j.z = m.row2.{x,y,z,w}
    lemma_dot_e2(bt.row0);
    lemma_dot_e2(bt.row1);
    lemma_dot_e2(bt.row2);
    lemma_dot_e2(bt.row3);
    // Row 3: dot(e3, bt.row_j) ≡ bt.row_j.w = m.row3.{x,y,z,w}
    lemma_dot_e3(bt.row0);
    lemma_dot_e3(bt.row1);
    lemma_dot_e3(bt.row2);
    lemma_dot_e3(bt.row3);
}

/// mat_mul(m, identity()).row_i ≡ m.row_i
pub proof fn lemma_identity_mat_mul_right<T: Ring>(m: Mat4x4<T>)
    ensures
        mat_mul(m, identity()).row0.eqv(m.row0),
        mat_mul(m, identity()).row1.eqv(m.row1),
        mat_mul(m, identity()).row2.eqv(m.row2),
        mat_mul(m, identity()).row3.eqv(m.row3),
{
    // transpose(identity()) = identity(), so columns of I are e0, e1, e2, e3
    lemma_dot_e0_right(m.row0);
    lemma_dot_e1_right(m.row0);
    lemma_dot_e2_right(m.row0);
    lemma_dot_e3_right(m.row0);
    lemma_dot_e0_right(m.row1);
    lemma_dot_e1_right(m.row1);
    lemma_dot_e2_right(m.row1);
    lemma_dot_e3_right(m.row1);
    lemma_dot_e0_right(m.row2);
    lemma_dot_e1_right(m.row2);
    lemma_dot_e2_right(m.row2);
    lemma_dot_e3_right(m.row2);
    lemma_dot_e0_right(m.row3);
    lemma_dot_e1_right(m.row3);
    lemma_dot_e2_right(m.row3);
    lemma_dot_e3_right(m.row3);
}

// ---------------------------------------------------------------------------
// Determinant lemmas
// ---------------------------------------------------------------------------

/// a - 0 ≡ a (private helper)
pub proof fn lemma_sub_zero_right<T: Ring>(a: T)
    ensures
        a.sub(T::zero()).eqv(a),
{
    T::axiom_sub_is_add_neg(a, T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a, T::zero().neg(), T::zero(),
    );
    T::axiom_add_zero_right(a);
    T::axiom_eqv_transitive(
        a.sub(T::zero()),
        a.add(T::zero().neg()),
        a.add(T::zero()),
    );
    T::axiom_eqv_transitive(
        a.sub(T::zero()),
        a.add(T::zero()),
        a,
    );
}

/// det(identity()) ≡ 1
pub proof fn lemma_det_identity<T: Ring>()
    ensures
        det(identity::<T>()).eqv(T::one()),
{
    // Cofactors along row 0 of identity:
    // row0 = (1, 0, 0, 0)
    // Only the first cofactor (with coefficient 1) contributes;
    // the rest have coefficient 0.
    //
    // The first minor is the 3×3 identity matrix, whose triple product = 1.
    // So det(I) = 1*1 - 0*? + 0*? - 0*? = 1 - 0 + 0 - 0 = 1.

    let e0 = Vec3::<T> { x: T::one(),  y: T::zero(), z: T::zero() };
    let e1 = Vec3::<T> { x: T::zero(), y: T::one(),  z: T::zero() };
    let e2 = Vec3::<T> { x: T::zero(), y: T::zero(), z: T::one()  };

    // drop_x of rows 1-3 of identity = (e0, e1, e2) in 3D
    // triple(e0, e1, e2) = det(I_3) ≡ 1
    crate::mat3::ops::lemma_det_identity::<T>();
    // det_identity gives det(I_3) ≡ 1, and det(I_3) = triple(e0, e1, e2) definitionally

    // 1 * triple(e0,e1,e2) ≡ 1 * 1 ≡ 1
    ring_lemmas::lemma_mul_congruence_right::<T>(T::one(), triple(e0, e1, e2), T::one());
    T::axiom_mul_one_right(T::one());
    T::axiom_eqv_transitive(
        T::one().mul(triple(e0, e1, e2)),
        T::one().mul(T::one()),
        T::one(),
    );

    // For the three zero-coefficient cofactors, 0 * anything ≡ 0
    let c1 = triple(
        drop_y(identity::<T>().row1), drop_y(identity::<T>().row2), drop_y(identity::<T>().row3),
    );
    let c2 = triple(
        drop_z(identity::<T>().row1), drop_z(identity::<T>().row2), drop_z(identity::<T>().row3),
    );
    let c3 = triple(
        drop_w(identity::<T>().row1), drop_w(identity::<T>().row2), drop_w(identity::<T>().row3),
    );
    ring_lemmas::lemma_mul_zero_left::<T>(c1);
    ring_lemmas::lemma_mul_zero_left::<T>(c2);
    ring_lemmas::lemma_mul_zero_left::<T>(c3);

    // det(I) = 1*triple(...) - 0*c1 + 0*c2 - 0*c3
    //        ≡ 1 - 0 + 0 - 0

    // Step: 1 - 0 ≡ 1
    additive_group_lemmas::lemma_sub_congruence::<T>(
        T::one().mul(triple(e0, e1, e2)), T::one(),
        T::zero().mul(c1), T::zero(),
    );
    lemma_sub_zero_right::<T>(T::one());
    T::axiom_eqv_transitive(
        T::one().mul(triple(e0, e1, e2)).sub(T::zero().mul(c1)),
        T::one().sub(T::zero()),
        T::one(),
    );

    // Step: 1 + 0 ≡ 1
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().mul(triple(e0, e1, e2)).sub(T::zero().mul(c1)), T::one(),
        T::zero().mul(c2), T::zero(),
    );
    T::axiom_add_zero_right(T::one());
    T::axiom_eqv_transitive(
        T::one().mul(triple(e0, e1, e2)).sub(T::zero().mul(c1)).add(T::zero().mul(c2)),
        T::one().add(T::zero()),
        T::one(),
    );

    // Step: 1 - 0 ≡ 1
    additive_group_lemmas::lemma_sub_congruence::<T>(
        T::one().mul(triple(e0, e1, e2)).sub(T::zero().mul(c1)).add(T::zero().mul(c2)), T::one(),
        T::zero().mul(c3), T::zero(),
    );
    lemma_sub_zero_right::<T>(T::one());
    T::axiom_eqv_transitive(
        det(identity::<T>()),
        T::one().sub(T::zero()),
        T::one(),
    );
}

/// Determinant respects row-wise equivalence
pub proof fn lemma_det_congruence<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    requires
        a.row0.eqv(b.row0),
        a.row1.eqv(b.row1),
        a.row2.eqv(b.row2),
        a.row3.eqv(b.row3),
    ensures
        det(a).eqv(det(b)),
{
    // For each cofactor, chain triple congruence (first → second → third)
    // then use mul_congruence with row0 component eqv.

    // Cofactor x
    lemma_triple_congruence_first(drop_x(a.row1), drop_x(b.row1), drop_x(a.row2), drop_x(a.row3));
    lemma_triple_congruence_second(drop_x(b.row1), drop_x(a.row2), drop_x(b.row2), drop_x(a.row3));
    lemma_triple_congruence_third(drop_x(b.row1), drop_x(b.row2), drop_x(a.row3), drop_x(b.row3));
    T::axiom_eqv_transitive(
        triple(drop_x(a.row1), drop_x(a.row2), drop_x(a.row3)),
        triple(drop_x(b.row1), drop_x(a.row2), drop_x(a.row3)),
        triple(drop_x(b.row1), drop_x(b.row2), drop_x(a.row3)),
    );
    T::axiom_eqv_transitive(
        triple(drop_x(a.row1), drop_x(a.row2), drop_x(a.row3)),
        triple(drop_x(b.row1), drop_x(b.row2), drop_x(a.row3)),
        triple(drop_x(b.row1), drop_x(b.row2), drop_x(b.row3)),
    );
    ring_lemmas::lemma_mul_congruence::<T>(
        a.row0.x, b.row0.x,
        triple(drop_x(a.row1), drop_x(a.row2), drop_x(a.row3)),
        triple(drop_x(b.row1), drop_x(b.row2), drop_x(b.row3)),
    );

    // Cofactor y
    lemma_triple_congruence_first(drop_y(a.row1), drop_y(b.row1), drop_y(a.row2), drop_y(a.row3));
    lemma_triple_congruence_second(drop_y(b.row1), drop_y(a.row2), drop_y(b.row2), drop_y(a.row3));
    lemma_triple_congruence_third(drop_y(b.row1), drop_y(b.row2), drop_y(a.row3), drop_y(b.row3));
    T::axiom_eqv_transitive(
        triple(drop_y(a.row1), drop_y(a.row2), drop_y(a.row3)),
        triple(drop_y(b.row1), drop_y(a.row2), drop_y(a.row3)),
        triple(drop_y(b.row1), drop_y(b.row2), drop_y(a.row3)),
    );
    T::axiom_eqv_transitive(
        triple(drop_y(a.row1), drop_y(a.row2), drop_y(a.row3)),
        triple(drop_y(b.row1), drop_y(b.row2), drop_y(a.row3)),
        triple(drop_y(b.row1), drop_y(b.row2), drop_y(b.row3)),
    );
    ring_lemmas::lemma_mul_congruence::<T>(
        a.row0.y, b.row0.y,
        triple(drop_y(a.row1), drop_y(a.row2), drop_y(a.row3)),
        triple(drop_y(b.row1), drop_y(b.row2), drop_y(b.row3)),
    );

    // Cofactor z
    lemma_triple_congruence_first(drop_z(a.row1), drop_z(b.row1), drop_z(a.row2), drop_z(a.row3));
    lemma_triple_congruence_second(drop_z(b.row1), drop_z(a.row2), drop_z(b.row2), drop_z(a.row3));
    lemma_triple_congruence_third(drop_z(b.row1), drop_z(b.row2), drop_z(a.row3), drop_z(b.row3));
    T::axiom_eqv_transitive(
        triple(drop_z(a.row1), drop_z(a.row2), drop_z(a.row3)),
        triple(drop_z(b.row1), drop_z(a.row2), drop_z(a.row3)),
        triple(drop_z(b.row1), drop_z(b.row2), drop_z(a.row3)),
    );
    T::axiom_eqv_transitive(
        triple(drop_z(a.row1), drop_z(a.row2), drop_z(a.row3)),
        triple(drop_z(b.row1), drop_z(b.row2), drop_z(a.row3)),
        triple(drop_z(b.row1), drop_z(b.row2), drop_z(b.row3)),
    );
    ring_lemmas::lemma_mul_congruence::<T>(
        a.row0.z, b.row0.z,
        triple(drop_z(a.row1), drop_z(a.row2), drop_z(a.row3)),
        triple(drop_z(b.row1), drop_z(b.row2), drop_z(b.row3)),
    );

    // Cofactor w
    lemma_triple_congruence_first(drop_w(a.row1), drop_w(b.row1), drop_w(a.row2), drop_w(a.row3));
    lemma_triple_congruence_second(drop_w(b.row1), drop_w(a.row2), drop_w(b.row2), drop_w(a.row3));
    lemma_triple_congruence_third(drop_w(b.row1), drop_w(b.row2), drop_w(a.row3), drop_w(b.row3));
    T::axiom_eqv_transitive(
        triple(drop_w(a.row1), drop_w(a.row2), drop_w(a.row3)),
        triple(drop_w(b.row1), drop_w(a.row2), drop_w(a.row3)),
        triple(drop_w(b.row1), drop_w(b.row2), drop_w(a.row3)),
    );
    T::axiom_eqv_transitive(
        triple(drop_w(a.row1), drop_w(a.row2), drop_w(a.row3)),
        triple(drop_w(b.row1), drop_w(b.row2), drop_w(a.row3)),
        triple(drop_w(b.row1), drop_w(b.row2), drop_w(b.row3)),
    );
    ring_lemmas::lemma_mul_congruence::<T>(
        a.row0.w, b.row0.w,
        triple(drop_w(a.row1), drop_w(a.row2), drop_w(a.row3)),
        triple(drop_w(b.row1), drop_w(b.row2), drop_w(b.row3)),
    );

    // Combine: (c0 - c1) + c2 - c3
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.row0.x.mul(triple(drop_x(a.row1), drop_x(a.row2), drop_x(a.row3))),
        b.row0.x.mul(triple(drop_x(b.row1), drop_x(b.row2), drop_x(b.row3))),
        a.row0.y.mul(triple(drop_y(a.row1), drop_y(a.row2), drop_y(a.row3))),
        b.row0.y.mul(triple(drop_y(b.row1), drop_y(b.row2), drop_y(b.row3))),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.row0.x.mul(triple(drop_x(a.row1), drop_x(a.row2), drop_x(a.row3)))
            .sub(a.row0.y.mul(triple(drop_y(a.row1), drop_y(a.row2), drop_y(a.row3)))),
        b.row0.x.mul(triple(drop_x(b.row1), drop_x(b.row2), drop_x(b.row3)))
            .sub(b.row0.y.mul(triple(drop_y(b.row1), drop_y(b.row2), drop_y(b.row3)))),
        a.row0.z.mul(triple(drop_z(a.row1), drop_z(a.row2), drop_z(a.row3))),
        b.row0.z.mul(triple(drop_z(b.row1), drop_z(b.row2), drop_z(b.row3))),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.row0.x.mul(triple(drop_x(a.row1), drop_x(a.row2), drop_x(a.row3)))
            .sub(a.row0.y.mul(triple(drop_y(a.row1), drop_y(a.row2), drop_y(a.row3))))
            .add(a.row0.z.mul(triple(drop_z(a.row1), drop_z(a.row2), drop_z(a.row3)))),
        b.row0.x.mul(triple(drop_x(b.row1), drop_x(b.row2), drop_x(b.row3)))
            .sub(b.row0.y.mul(triple(drop_y(b.row1), drop_y(b.row2), drop_y(b.row3))))
            .add(b.row0.z.mul(triple(drop_z(b.row1), drop_z(b.row2), drop_z(b.row3)))),
        a.row0.w.mul(triple(drop_w(a.row1), drop_w(a.row2), drop_w(a.row3))),
        b.row0.w.mul(triple(drop_w(b.row1), drop_w(b.row2), drop_w(b.row3))),
    );
}

// ---------------------------------------------------------------------------
// Mat-vec-mul associativity infrastructure
// ---------------------------------------------------------------------------

/// Helper: s * dot(u, v) ≡ (s*u.x)*v.x + (s*u.y)*v.y + (s*u.z)*v.z + (s*u.w)*v.w
pub proof fn lemma_distribute_scalar_dot4<T: Ring>(s: T, u: Vec4<T>, v: Vec4<T>)
    ensures
        s.mul(dot(u, v)).eqv(
            s.mul(u.x).mul(v.x).add(s.mul(u.y).mul(v.y))
                .add(s.mul(u.z).mul(v.z)).add(s.mul(u.w).mul(v.w))
        ),
{
    // dot(u, v) = ((u.x*v.x + u.y*v.y) + u.z*v.z) + u.w*v.w
    // s * (((A + B) + C) + D) ≡ s*(A+B+C) + s*D ≡ s*(A+B) + s*C + s*D ≡ s*A + s*B + s*C + s*D
    T::axiom_mul_distributes_left(s, u.x.mul(v.x).add(u.y.mul(v.y)).add(u.z.mul(v.z)), u.w.mul(v.w));
    T::axiom_mul_distributes_left(s, u.x.mul(v.x).add(u.y.mul(v.y)), u.z.mul(v.z));
    T::axiom_mul_distributes_left(s, u.x.mul(v.x), u.y.mul(v.y));

    // s*(u.i*v.i) ≡ (s*u.i)*v.i for each i
    T::axiom_mul_associative(s, u.x, v.x);
    T::axiom_eqv_symmetric(s.mul(u.x).mul(v.x), s.mul(u.x.mul(v.x)));
    T::axiom_mul_associative(s, u.y, v.y);
    T::axiom_eqv_symmetric(s.mul(u.y).mul(v.y), s.mul(u.y.mul(v.y)));
    T::axiom_mul_associative(s, u.z, v.z);
    T::axiom_eqv_symmetric(s.mul(u.z).mul(v.z), s.mul(u.z.mul(v.z)));
    T::axiom_mul_associative(s, u.w, v.w);
    T::axiom_eqv_symmetric(s.mul(u.w).mul(v.w), s.mul(u.w.mul(v.w)));

    // Combine inner pair: s*(u.x*v.x) + s*(u.y*v.y) ≡ (s*u.x)*v.x + (s*u.y)*v.y
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(u.x.mul(v.x)), s.mul(u.x).mul(v.x),
        s.mul(u.y.mul(v.y)), s.mul(u.y).mul(v.y),
    );
    // Chain: s*(u.x*v.x + u.y*v.y) ≡ (s*u.x)*v.x + (s*u.y)*v.y
    T::axiom_eqv_transitive(
        s.mul(u.x.mul(v.x).add(u.y.mul(v.y))),
        s.mul(u.x.mul(v.x)).add(s.mul(u.y.mul(v.y))),
        s.mul(u.x).mul(v.x).add(s.mul(u.y).mul(v.y)),
    );

    // Add z: (...) + s*(u.z*v.z) ≡ (...) + (s*u.z)*v.z
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(u.x.mul(v.x).add(u.y.mul(v.y))),
        s.mul(u.x).mul(v.x).add(s.mul(u.y).mul(v.y)),
        s.mul(u.z.mul(v.z)),
        s.mul(u.z).mul(v.z),
    );
    // Chain: s*((u.x*v.x + u.y*v.y) + u.z*v.z) ≡ (s*u.x)*v.x + (s*u.y)*v.y + (s*u.z)*v.z
    T::axiom_eqv_transitive(
        s.mul(u.x.mul(v.x).add(u.y.mul(v.y)).add(u.z.mul(v.z))),
        s.mul(u.x.mul(v.x).add(u.y.mul(v.y))).add(s.mul(u.z.mul(v.z))),
        s.mul(u.x).mul(v.x).add(s.mul(u.y).mul(v.y)).add(s.mul(u.z).mul(v.z)),
    );

    // Add w: (...) + s*(u.w*v.w) ≡ (...) + (s*u.w)*v.w
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(u.x.mul(v.x).add(u.y.mul(v.y)).add(u.z.mul(v.z))),
        s.mul(u.x).mul(v.x).add(s.mul(u.y).mul(v.y)).add(s.mul(u.z).mul(v.z)),
        s.mul(u.w.mul(v.w)),
        s.mul(u.w).mul(v.w),
    );
    // Chain: s * dot(u, v) ≡ result
    T::axiom_eqv_transitive(
        s.mul(dot(u, v)),
        s.mul(u.x.mul(v.x).add(u.y.mul(v.y)).add(u.z.mul(v.z))).add(s.mul(u.w.mul(v.w))),
        s.mul(u.x).mul(v.x).add(s.mul(u.y).mul(v.y)).add(s.mul(u.z).mul(v.z)).add(s.mul(u.w).mul(v.w)),
    );
}

/// Rearrange 16 terms from row-major to column-major grouping.
/// (((a0+a1)+a2)+a3) + (((b0+b1)+b2)+b3) + (((c0+c1)+c2)+c3) + (((d0+d1)+d2)+d3)
/// ≡ (((a0+b0)+c0)+d0) + (((a1+b1)+c1)+d1) + (((a2+b2)+c2)+d2) + (((a3+b3)+c3)+d3)
pub proof fn lemma_add_rearrange_4x4<T: Ring>(
    a0: T, a1: T, a2: T, a3: T,
    b0: T, b1: T, b2: T, b3: T,
    c0: T, c1: T, c2: T, c3: T,
    d0: T, d1: T, d2: T, d3: T,
)
    ensures
        a0.add(a1).add(a2).add(a3)
            .add(b0.add(b1).add(b2).add(b3))
            .add(c0.add(c1).add(c2).add(c3))
            .add(d0.add(d1).add(d2).add(d3))
        .eqv(
            a0.add(b0).add(c0).add(d0)
                .add(a1.add(b1).add(c1).add(d1))
                .add(a2.add(b2).add(c2).add(d2))
                .add(a3.add(b3).add(c3).add(d3))
        ),
{
    // Strategy: use rearrange_2x2 cascaded.
    // First pair rows (A,B): rearrange into column pairs, then pair with (C,D).

    let a = a0.add(a1).add(a2).add(a3);
    let b = b0.add(b1).add(b2).add(b3);
    let c = c0.add(c1).add(c2).add(c3);
    let d = d0.add(d1).add(d2).add(d3);

    // === Phase 2: A+B ≡ ((ab0+ab1)+ab2)+ab3 via cascading rearrange_2x2 ===
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a0.add(a1).add(a2), a3, b0.add(b1).add(b2), b3);
    //   then rearrange_2x2(a0+a1, a2, b0+b1, b2) on the first part
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a0.add(a1), a2, b0.add(b1), b2);
    //   then rearrange_2x2(a0, a1, b0, b1) on the first part of that
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a0, a1, b0, b1);

    // Substitute inner: (a0+a1)+(b0+b1) ≡ (a0+b0)+(a1+b1)
    T::axiom_add_congruence_left(
        a0.add(a1).add(b0.add(b1)), a0.add(b0).add(a1.add(b1)),
        a2.add(b2),
    );
    // ((a0+a1)+(b0+b1))+(a2+b2) ≡ ((a0+b0)+(a1+b1))+(a2+b2)
    T::axiom_eqv_transitive(
        a0.add(a1).add(a2).add(b0.add(b1).add(b2)),
        a0.add(a1).add(b0.add(b1)).add(a2.add(b2)),
        a0.add(b0).add(a1.add(b1)).add(a2.add(b2)),
    );

    // Substitute into outer:
    T::axiom_add_congruence_left(
        a0.add(a1).add(a2).add(b0.add(b1).add(b2)),
        a0.add(b0).add(a1.add(b1)).add(a2.add(b2)),
        a3.add(b3),
    );
    T::axiom_eqv_transitive(
        a.add(b),
        a0.add(a1).add(a2).add(b0.add(b1).add(b2)).add(a3.add(b3)),
        a0.add(b0).add(a1.add(b1)).add(a2.add(b2)).add(a3.add(b3)),
    );
    // A+B ≡ ((a0+b0)+(a1+b1)+(a2+b2))+(a3+b3)

    // Same for C+D
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(c0.add(c1).add(c2), c3, d0.add(d1).add(d2), d3);
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(c0.add(c1), c2, d0.add(d1), d2);
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(c0, c1, d0, d1);
    T::axiom_add_congruence_left(
        c0.add(c1).add(d0.add(d1)), c0.add(d0).add(c1.add(d1)),
        c2.add(d2),
    );
    T::axiom_eqv_transitive(
        c0.add(c1).add(c2).add(d0.add(d1).add(d2)),
        c0.add(c1).add(d0.add(d1)).add(c2.add(d2)),
        c0.add(d0).add(c1.add(d1)).add(c2.add(d2)),
    );
    T::axiom_add_congruence_left(
        c0.add(c1).add(c2).add(d0.add(d1).add(d2)),
        c0.add(d0).add(c1.add(d1)).add(c2.add(d2)),
        c3.add(d3),
    );
    T::axiom_eqv_transitive(
        c.add(d),
        c0.add(c1).add(c2).add(d0.add(d1).add(d2)).add(c3.add(d3)),
        c0.add(d0).add(c1.add(d1)).add(c2.add(d2)).add(c3.add(d3)),
    );
    // C+D ≡ ((c0+d0)+(c1+d1)+(c2+d2))+(c3+d3)

    // Now combine (A+B)+(C+D):
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(b),
        a0.add(b0).add(a1.add(b1)).add(a2.add(b2)).add(a3.add(b3)),
        c.add(d),
        c0.add(d0).add(c1.add(d1)).add(c2.add(d2)).add(c3.add(d3)),
    );

    // (A+B)+(C+D):  rearrange the two 4-term results
    let ab0 = a0.add(b0);
    let ab1 = a1.add(b1);
    let ab2 = a2.add(b2);
    let ab3 = a3.add(b3);
    let cd0 = c0.add(d0);
    let cd1 = c1.add(d1);
    let cd2 = c2.add(d2);
    let cd3 = c3.add(d3);

    // (ab0+ab1+ab2+ab3) + (cd0+cd1+cd2+cd3) via same rearrange
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(ab0.add(ab1).add(ab2), ab3, cd0.add(cd1).add(cd2), cd3);
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(ab0.add(ab1), ab2, cd0.add(cd1), cd2);
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(ab0, ab1, cd0, cd1);

    T::axiom_add_congruence_left(
        ab0.add(ab1).add(cd0.add(cd1)), ab0.add(cd0).add(ab1.add(cd1)),
        ab2.add(cd2),
    );
    T::axiom_eqv_transitive(
        ab0.add(ab1).add(ab2).add(cd0.add(cd1).add(cd2)),
        ab0.add(ab1).add(cd0.add(cd1)).add(ab2.add(cd2)),
        ab0.add(cd0).add(ab1.add(cd1)).add(ab2.add(cd2)),
    );
    T::axiom_add_congruence_left(
        ab0.add(ab1).add(ab2).add(cd0.add(cd1).add(cd2)),
        ab0.add(cd0).add(ab1.add(cd1)).add(ab2.add(cd2)),
        ab3.add(cd3),
    );
    T::axiom_eqv_transitive(
        ab0.add(ab1).add(ab2).add(ab3).add(cd0.add(cd1).add(cd2).add(cd3)),
        ab0.add(ab1).add(ab2).add(cd0.add(cd1).add(cd2)).add(ab3.add(cd3)),
        ab0.add(cd0).add(ab1.add(cd1)).add(ab2.add(cd2)).add(ab3.add(cd3)),
    );

    // Chain: (A+B)+(C+D) ≡ AB_vec + CD_vec ≡ paired_form
    T::axiom_eqv_transitive(
        a.add(b).add(c.add(d)),
        ab0.add(ab1).add(ab2).add(ab3).add(cd0.add(cd1).add(cd2).add(cd3)),
        ab0.add(cd0).add(ab1.add(cd1)).add(ab2.add(cd2)).add(ab3.add(cd3)),
    );

    // Convert (ABj+CDj) = (aj+bj)+(cj+dj) to colj = ((aj+bj)+cj)+dj
    // axiom_add_associative gives colj ≡ ABj+CDj, symmetric flips it
    T::axiom_add_associative(ab0, c0, d0);
    T::axiom_eqv_symmetric(ab0.add(c0).add(d0), ab0.add(cd0));
    T::axiom_add_associative(ab1, c1, d1);
    T::axiom_eqv_symmetric(ab1.add(c1).add(d1), ab1.add(cd1));
    T::axiom_add_associative(ab2, c2, d2);
    T::axiom_eqv_symmetric(ab2.add(c2).add(d2), ab2.add(cd2));
    T::axiom_add_associative(ab3, c3, d3);
    T::axiom_eqv_symmetric(ab3.add(c3).add(d3), ab3.add(cd3));

    // Propagate conversion through the 4-term sum
    lemma_add_congruence_4::<T>(
        ab0.add(cd0), ab0.add(c0).add(d0),
        ab1.add(cd1), ab1.add(c1).add(d1),
        ab2.add(cd2), ab2.add(c2).add(d2),
        ab3.add(cd3), ab3.add(c3).add(d3),
    );
    // paired_form ≡ RHS

    // Chain: (A+B)+(C+D) ≡ paired_form ≡ RHS
    T::axiom_eqv_transitive(
        a.add(b).add(c.add(d)),
        ab0.add(cd0).add(ab1.add(cd1)).add(ab2.add(cd2)).add(ab3.add(cd3)),
        ab0.add(c0).add(d0).add(ab1.add(c1).add(d1)).add(ab2.add(c2).add(d2)).add(ab3.add(c3).add(d3)),
    );

    // Final: ((A+B)+C)+D ≡ (A+B)+(C+D) ≡ RHS
    T::axiom_add_associative(a.add(b), c, d);
    T::axiom_eqv_transitive(
        a.add(b).add(c).add(d),
        a.add(b).add(c.add(d)),
        ab0.add(c0).add(d0).add(ab1.add(c1).add(d1)).add(ab2.add(c2).add(d2)).add(ab3.add(c3).add(d3)),
    );
}

/// Factor 4 additive terms over a common right factor:
/// ((p*z + q*z) + r*z) + s*z ≡ (((p+q)+r)+s)*z
pub proof fn lemma_factor_4<T: Ring>(p: T, q: T, r: T, s: T, z: T)
    ensures
        p.mul(z).add(q.mul(z)).add(r.mul(z)).add(s.mul(z)).eqv(
            p.add(q).add(r).add(s).mul(z)
        ),
{
    // (p+q)*z ≡ p*z + q*z
    ring_lemmas::lemma_mul_distributes_right::<T>(p, q, z);
    T::axiom_eqv_symmetric(p.add(q).mul(z), p.mul(z).add(q.mul(z)));
    // ((p+q)+r)*z ≡ (p+q)*z + r*z
    ring_lemmas::lemma_mul_distributes_right::<T>(p.add(q), r, z);
    T::axiom_eqv_symmetric(p.add(q).add(r).mul(z), p.add(q).mul(z).add(r.mul(z)));
    // (((p+q)+r)+s)*z ≡ ((p+q)+r)*z + s*z
    ring_lemmas::lemma_mul_distributes_right::<T>(p.add(q).add(r), s, z);
    T::axiom_eqv_symmetric(p.add(q).add(r).add(s).mul(z), p.add(q).add(r).mul(z).add(s.mul(z)));

    // p*z+q*z ≡ (p+q)*z
    T::axiom_add_congruence_left(p.mul(z).add(q.mul(z)), p.add(q).mul(z), r.mul(z));
    // (p*z+q*z)+r*z ≡ (p+q)*z + r*z ≡ ((p+q)+r)*z
    T::axiom_eqv_transitive(
        p.mul(z).add(q.mul(z)).add(r.mul(z)),
        p.add(q).mul(z).add(r.mul(z)),
        p.add(q).add(r).mul(z),
    );
    // ((p*z+q*z)+r*z)+s*z ≡ ((p+q)+r)*z + s*z ≡ (((p+q)+r)+s)*z
    T::axiom_add_congruence_left(
        p.mul(z).add(q.mul(z)).add(r.mul(z)),
        p.add(q).add(r).mul(z),
        s.mul(z),
    );
    T::axiom_eqv_transitive(
        p.mul(z).add(q.mul(z)).add(r.mul(z)).add(s.mul(z)),
        p.add(q).add(r).mul(z).add(s.mul(z)),
        p.add(q).add(r).add(s).mul(z),
    );
}

/// 4-term additive congruence
pub proof fn lemma_add_congruence_4<T: Ring>(
    a1: T, a2: T, b1: T, b2: T, c1: T, c2: T, d1: T, d2: T,
)
    requires a1.eqv(a2), b1.eqv(b2), c1.eqv(c2), d1.eqv(d2),
    ensures a1.add(b1).add(c1).add(d1).eqv(a2.add(b2).add(c2).add(d2)),
{
    additive_group_lemmas::lemma_add_congruence::<T>(a1, a2, b1, b2);
    additive_group_lemmas::lemma_add_congruence::<T>(a1.add(b1), a2.add(b2), c1, c2);
    additive_group_lemmas::lemma_add_congruence::<T>(a1.add(b1).add(c1), a2.add(b2).add(c2), d1, d2);
}

/// Helper: for any row vector ai and matrix b,
/// dot(ai, mat_vec_mul(b, v)) ≡ dot(ai, bt.col0)*v.x + ... + dot(ai, bt.col3)*v.w
pub proof fn lemma_dot_mat_vec_mul_row<T: Ring>(ai: Vec4<T>, b: Mat4x4<T>, v: Vec4<T>)
    ensures
        dot(ai, mat_vec_mul(b, v)).eqv(
            dot(ai, transpose(b).row0).mul(v.x)
                .add(dot(ai, transpose(b).row1).mul(v.y))
                .add(dot(ai, transpose(b).row2).mul(v.z))
                .add(dot(ai, transpose(b).row3).mul(v.w))
        ),
{
    // Step 1: distribute each scalar into its dot product
    lemma_distribute_scalar_dot4(ai.x, b.row0, v);
    lemma_distribute_scalar_dot4(ai.y, b.row1, v);
    lemma_distribute_scalar_dot4(ai.z, b.row2, v);
    lemma_distribute_scalar_dot4(ai.w, b.row3, v);

    // Step 2: combine all four distributed forms
    lemma_add_congruence_4::<T>(
        ai.x.mul(dot(b.row0, v)),
        ai.x.mul(b.row0.x).mul(v.x).add(ai.x.mul(b.row0.y).mul(v.y)).add(ai.x.mul(b.row0.z).mul(v.z)).add(ai.x.mul(b.row0.w).mul(v.w)),
        ai.y.mul(dot(b.row1, v)),
        ai.y.mul(b.row1.x).mul(v.x).add(ai.y.mul(b.row1.y).mul(v.y)).add(ai.y.mul(b.row1.z).mul(v.z)).add(ai.y.mul(b.row1.w).mul(v.w)),
        ai.z.mul(dot(b.row2, v)),
        ai.z.mul(b.row2.x).mul(v.x).add(ai.z.mul(b.row2.y).mul(v.y)).add(ai.z.mul(b.row2.z).mul(v.z)).add(ai.z.mul(b.row2.w).mul(v.w)),
        ai.w.mul(dot(b.row3, v)),
        ai.w.mul(b.row3.x).mul(v.x).add(ai.w.mul(b.row3.y).mul(v.y)).add(ai.w.mul(b.row3.z).mul(v.z)).add(ai.w.mul(b.row3.w).mul(v.w)),
    );

    // Step 3: rearrange from row-major to column-major grouping
    lemma_add_rearrange_4x4(
        ai.x.mul(b.row0.x).mul(v.x), ai.x.mul(b.row0.y).mul(v.y), ai.x.mul(b.row0.z).mul(v.z), ai.x.mul(b.row0.w).mul(v.w),
        ai.y.mul(b.row1.x).mul(v.x), ai.y.mul(b.row1.y).mul(v.y), ai.y.mul(b.row1.z).mul(v.z), ai.y.mul(b.row1.w).mul(v.w),
        ai.z.mul(b.row2.x).mul(v.x), ai.z.mul(b.row2.y).mul(v.y), ai.z.mul(b.row2.z).mul(v.z), ai.z.mul(b.row2.w).mul(v.w),
        ai.w.mul(b.row3.x).mul(v.x), ai.w.mul(b.row3.y).mul(v.y), ai.w.mul(b.row3.z).mul(v.z), ai.w.mul(b.row3.w).mul(v.w),
    );

    // Step 4: factor v.x, v.y, v.z, v.w from each column-group
    lemma_factor_4(ai.x.mul(b.row0.x), ai.y.mul(b.row1.x), ai.z.mul(b.row2.x), ai.w.mul(b.row3.x), v.x);
    lemma_factor_4(ai.x.mul(b.row0.y), ai.y.mul(b.row1.y), ai.z.mul(b.row2.y), ai.w.mul(b.row3.y), v.y);
    lemma_factor_4(ai.x.mul(b.row0.z), ai.y.mul(b.row1.z), ai.z.mul(b.row2.z), ai.w.mul(b.row3.z), v.z);
    lemma_factor_4(ai.x.mul(b.row0.w), ai.y.mul(b.row1.w), ai.z.mul(b.row2.w), ai.w.mul(b.row3.w), v.w);

    // Step 5: combine the factored groups
    lemma_add_congruence_4::<T>(
        ai.x.mul(b.row0.x).mul(v.x).add(ai.y.mul(b.row1.x).mul(v.x)).add(ai.z.mul(b.row2.x).mul(v.x)).add(ai.w.mul(b.row3.x).mul(v.x)),
        ai.x.mul(b.row0.x).add(ai.y.mul(b.row1.x)).add(ai.z.mul(b.row2.x)).add(ai.w.mul(b.row3.x)).mul(v.x),
        ai.x.mul(b.row0.y).mul(v.y).add(ai.y.mul(b.row1.y).mul(v.y)).add(ai.z.mul(b.row2.y).mul(v.y)).add(ai.w.mul(b.row3.y).mul(v.y)),
        ai.x.mul(b.row0.y).add(ai.y.mul(b.row1.y)).add(ai.z.mul(b.row2.y)).add(ai.w.mul(b.row3.y)).mul(v.y),
        ai.x.mul(b.row0.z).mul(v.z).add(ai.y.mul(b.row1.z).mul(v.z)).add(ai.z.mul(b.row2.z).mul(v.z)).add(ai.w.mul(b.row3.z).mul(v.z)),
        ai.x.mul(b.row0.z).add(ai.y.mul(b.row1.z)).add(ai.z.mul(b.row2.z)).add(ai.w.mul(b.row3.z)).mul(v.z),
        ai.x.mul(b.row0.w).mul(v.w).add(ai.y.mul(b.row1.w).mul(v.w)).add(ai.z.mul(b.row2.w).mul(v.w)).add(ai.w.mul(b.row3.w).mul(v.w)),
        ai.x.mul(b.row0.w).add(ai.y.mul(b.row1.w)).add(ai.z.mul(b.row2.w)).add(ai.w.mul(b.row3.w)).mul(v.w),
    );

    // Step 6: chain lhs ≡ dist ≡ rear ≡ fact
    let lhs = ai.x.mul(dot(b.row0, v))
        .add(ai.y.mul(dot(b.row1, v)))
        .add(ai.z.mul(dot(b.row2, v)))
        .add(ai.w.mul(dot(b.row3, v)));
    let dist = ai.x.mul(b.row0.x).mul(v.x).add(ai.x.mul(b.row0.y).mul(v.y)).add(ai.x.mul(b.row0.z).mul(v.z)).add(ai.x.mul(b.row0.w).mul(v.w))
        .add(ai.y.mul(b.row1.x).mul(v.x).add(ai.y.mul(b.row1.y).mul(v.y)).add(ai.y.mul(b.row1.z).mul(v.z)).add(ai.y.mul(b.row1.w).mul(v.w)))
        .add(ai.z.mul(b.row2.x).mul(v.x).add(ai.z.mul(b.row2.y).mul(v.y)).add(ai.z.mul(b.row2.z).mul(v.z)).add(ai.z.mul(b.row2.w).mul(v.w)))
        .add(ai.w.mul(b.row3.x).mul(v.x).add(ai.w.mul(b.row3.y).mul(v.y)).add(ai.w.mul(b.row3.z).mul(v.z)).add(ai.w.mul(b.row3.w).mul(v.w)));
    let rear = ai.x.mul(b.row0.x).mul(v.x).add(ai.y.mul(b.row1.x).mul(v.x)).add(ai.z.mul(b.row2.x).mul(v.x)).add(ai.w.mul(b.row3.x).mul(v.x))
        .add(ai.x.mul(b.row0.y).mul(v.y).add(ai.y.mul(b.row1.y).mul(v.y)).add(ai.z.mul(b.row2.y).mul(v.y)).add(ai.w.mul(b.row3.y).mul(v.y)))
        .add(ai.x.mul(b.row0.z).mul(v.z).add(ai.y.mul(b.row1.z).mul(v.z)).add(ai.z.mul(b.row2.z).mul(v.z)).add(ai.w.mul(b.row3.z).mul(v.z)))
        .add(ai.x.mul(b.row0.w).mul(v.w).add(ai.y.mul(b.row1.w).mul(v.w)).add(ai.z.mul(b.row2.w).mul(v.w)).add(ai.w.mul(b.row3.w).mul(v.w)));
    let fact = ai.x.mul(b.row0.x).add(ai.y.mul(b.row1.x)).add(ai.z.mul(b.row2.x)).add(ai.w.mul(b.row3.x)).mul(v.x)
        .add(ai.x.mul(b.row0.y).add(ai.y.mul(b.row1.y)).add(ai.z.mul(b.row2.y)).add(ai.w.mul(b.row3.y)).mul(v.y))
        .add(ai.x.mul(b.row0.z).add(ai.y.mul(b.row1.z)).add(ai.z.mul(b.row2.z)).add(ai.w.mul(b.row3.z)).mul(v.z))
        .add(ai.x.mul(b.row0.w).add(ai.y.mul(b.row1.w)).add(ai.z.mul(b.row2.w)).add(ai.w.mul(b.row3.w)).mul(v.w));

    T::axiom_eqv_transitive(lhs, dist, rear);
    T::axiom_eqv_transitive(lhs, rear, fact);
}

/// mat_vec_mul(a, mat_vec_mul(b, v)) ≡ mat_vec_mul(mat_mul(a, b), v)
pub proof fn lemma_mat_vec_mul_mat_mul<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>, v: Vec4<T>)
    ensures
        mat_vec_mul(a, mat_vec_mul(b, v)).eqv(mat_vec_mul(mat_mul(a, b), v)),
{
    lemma_dot_mat_vec_mul_row(a.row0, b, v);
    lemma_dot_mat_vec_mul_row(a.row1, b, v);
    lemma_dot_mat_vec_mul_row(a.row2, b, v);
    lemma_dot_mat_vec_mul_row(a.row3, b, v);
}

// ---------------------------------------------------------------------------
// Cross-checking lemmas
// ---------------------------------------------------------------------------

/// mat_mul(a, mat_mul(b, c)).row_i ≡ mat_mul(mat_mul(a, b), c).row_i
pub proof fn lemma_mat_mul_associative<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>, c: Mat4x4<T>)
    ensures
        mat_mul(a, mat_mul(b, c)).row0.eqv(mat_mul(mat_mul(a, b), c).row0),
        mat_mul(a, mat_mul(b, c)).row1.eqv(mat_mul(mat_mul(a, b), c).row1),
        mat_mul(a, mat_mul(b, c)).row2.eqv(mat_mul(mat_mul(a, b), c).row2),
        mat_mul(a, mat_mul(b, c)).row3.eqv(mat_mul(mat_mul(a, b), c).row3),
{
    let ct = transpose(c);
    // For each column j of c (= row j of ct):
    // mat_mul(a*b, c).row_i.j = dot(mat_mul(a,b).row_i, ct.row_j)
    //   = mat_vec_mul(a*b, ct.row_j).component_i  [by definition of mat_mul]
    // mat_vec_mul(a*b, ct.row_j) ≡ mat_vec_mul(a, mat_vec_mul(b, ct.row_j))
    //   [by lemma_mat_vec_mul_mat_mul]
    // mat_vec_mul(a, mat_vec_mul(b, ct.row_j)).component_i
    //   = dot(a.row_i, mat_vec_mul(b, ct.row_j))
    //   = dot(a.row_i, transpose(b*c).row_j)     [since mat_vec_mul(b, ct.row_j) = (b*c) col j]
    //   = mat_mul(a, b*c).row_i.component_j
    lemma_mat_vec_mul_mat_mul(a, b, ct.row0);
    lemma_mat_vec_mul_mat_mul(a, b, ct.row1);
    lemma_mat_vec_mul_mat_mul(a, b, ct.row2);
    lemma_mat_vec_mul_mat_mul(a, b, ct.row3);
}

/// transpose(mat_mul(a, b)).row_i ≡ mat_mul(transpose(b), transpose(a)).row_i
pub proof fn lemma_transpose_mat_mul<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        transpose(mat_mul(a, b)).row0.eqv(mat_mul(transpose(b), transpose(a)).row0),
        transpose(mat_mul(a, b)).row1.eqv(mat_mul(transpose(b), transpose(a)).row1),
        transpose(mat_mul(a, b)).row2.eqv(mat_mul(transpose(b), transpose(a)).row2),
        transpose(mat_mul(a, b)).row3.eqv(mat_mul(transpose(b), transpose(a)).row3),
{
    let bt = transpose(b);
    let at = transpose(a);
    // transpose(a*b).row_i.j = (a*b).row_j.i = dot(a.row_j, bt.row_i)
    // (bt*at).row_i.j = dot(bt.row_i, transpose(at).row_j) = dot(bt.row_i, a.row_j)
    // dot(a.row_j, bt.row_i) ≡ dot(bt.row_i, a.row_j) by commutativity
    crate::vec4::ops::lemma_dot_commutative(a.row0, bt.row0);
    crate::vec4::ops::lemma_dot_commutative(a.row1, bt.row0);
    crate::vec4::ops::lemma_dot_commutative(a.row2, bt.row0);
    crate::vec4::ops::lemma_dot_commutative(a.row3, bt.row0);

    crate::vec4::ops::lemma_dot_commutative(a.row0, bt.row1);
    crate::vec4::ops::lemma_dot_commutative(a.row1, bt.row1);
    crate::vec4::ops::lemma_dot_commutative(a.row2, bt.row1);
    crate::vec4::ops::lemma_dot_commutative(a.row3, bt.row1);

    crate::vec4::ops::lemma_dot_commutative(a.row0, bt.row2);
    crate::vec4::ops::lemma_dot_commutative(a.row1, bt.row2);
    crate::vec4::ops::lemma_dot_commutative(a.row2, bt.row2);
    crate::vec4::ops::lemma_dot_commutative(a.row3, bt.row2);

    crate::vec4::ops::lemma_dot_commutative(a.row0, bt.row3);
    crate::vec4::ops::lemma_dot_commutative(a.row1, bt.row3);
    crate::vec4::ops::lemma_dot_commutative(a.row2, bt.row3);
    crate::vec4::ops::lemma_dot_commutative(a.row3, bt.row3);
}

} // verus!
