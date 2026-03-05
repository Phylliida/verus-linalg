use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use crate::vec3::Vec3;
use crate::vec3::ops::{triple, lemma_triple_congruence_first, lemma_triple_congruence_second, lemma_triple_congruence_third, lemma_triple_swap_12, lemma_triple_swap_23, lemma_triple_self_zero_12, lemma_triple_self_zero_23, lemma_triple_self_zero_13, lemma_triple_linear_first, lemma_triple_scale_first, lemma_triple_neg_first};
use crate::vec4::Vec4;
use crate::vec4::ops::{dot, scale};
use super::Mat4x4;
use verus_algebra::lemmas::field_lemmas;

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

// ---------------------------------------------------------------------------
// Phase 1: Easy det properties + helpers
// ---------------------------------------------------------------------------

/// Signed cofactor vector for Laplace expansion along row 0.
/// det(m) ≡ dot(row0, cofactor_vec(row1, row2, row3)).
pub open spec fn cofactor_vec<T: Ring>(r1: Vec4<T>, r2: Vec4<T>, r3: Vec4<T>) -> Vec4<T> {
    Vec4 {
        x: triple(drop_x(r1), drop_x(r2), drop_x(r3)),
        y: triple(drop_y(r1), drop_y(r2), drop_y(r3)).neg(),
        z: triple(drop_z(r1), drop_z(r2), drop_z(r3)),
        w: triple(drop_w(r1), drop_w(r2), drop_w(r3)).neg(),
    }
}

/// det(m) ≡ dot(row0, cofactor_vec(row1, row2, row3)).
/// Bridges sub-based det definition with add-based dot definition.
pub proof fn lemma_det_as_dot<T: Ring>(m: Mat4x4<T>)
    ensures
        det(m).eqv(dot(m.row0, cofactor_vec(m.row1, m.row2, m.row3))),
{
    let r0 = m.row0;
    let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;
    let tx = triple(drop_x(r1), drop_x(r2), drop_x(r3));
    let ty = triple(drop_y(r1), drop_y(r2), drop_y(r3));
    let tz = triple(drop_z(r1), drop_z(r2), drop_z(r3));
    let tw = triple(drop_w(r1), drop_w(r2), drop_w(r3));
    let a = r0.x.mul(tx);
    let b = r0.y.mul(ty);
    let c = r0.z.mul(tz);
    let d = r0.w.mul(tw);

    // det = A.sub(B).add(C).sub(D)
    // dot = A.add(r0.y.mul(ty.neg())).add(C).add(r0.w.mul(tw.neg()))

    // Step 1: Convert det from sub to add(neg) form using sub_is_add_neg
    T::axiom_sub_is_add_neg(a, b);
    // A.sub(B) ≡ A.add(B.neg())
    T::axiom_add_congruence_left(a.sub(b), a.add(b.neg()), c);
    // A.sub(B).add(C) ≡ A.add(B.neg()).add(C)
    T::axiom_sub_is_add_neg(a.sub(b).add(c), d);
    // A.sub(B).add(C).sub(D) ≡ A.sub(B).add(C).add(D.neg())
    T::axiom_add_congruence_left(a.sub(b).add(c), a.add(b.neg()).add(c), d.neg());
    // A.sub(B).add(C).add(D.neg()) ≡ A.add(B.neg()).add(C).add(D.neg())
    T::axiom_eqv_transitive(
        a.sub(b).add(c).sub(d),
        a.sub(b).add(c).add(d.neg()),
        a.add(b.neg()).add(c).add(d.neg()),
    );
    // det ≡ A.add(B.neg()).add(C).add(D.neg())

    // Step 2: Bridge B.neg() ↔ r0.y.mul(ty.neg()) and D.neg() ↔ r0.w.mul(tw.neg())
    // mul_neg_right: a*(-b) ≡ -(a*b), so r0.y.mul(ty.neg()) ≡ (r0.y.mul(ty)).neg() = B.neg()
    ring_lemmas::lemma_mul_neg_right(r0.y, ty);
    // r0.y.mul(ty.neg()).eqv(b.neg())
    T::axiom_eqv_symmetric(r0.y.mul(ty.neg()), b.neg());
    // B.neg() ≡ r0.y.mul(ty.neg())

    ring_lemmas::lemma_mul_neg_right(r0.w, tw);
    T::axiom_eqv_symmetric(r0.w.mul(tw.neg()), d.neg());
    // D.neg() ≡ r0.w.mul(tw.neg())

    // Substitute: A.add(B.neg()) ≡ A.add(r0.y.mul(ty.neg()))
    additive_group_lemmas::lemma_add_congruence_right::<T>(a, b.neg(), r0.y.mul(ty.neg()));
    // .add(C) on both sides
    T::axiom_add_congruence_left(a.add(b.neg()), a.add(r0.y.mul(ty.neg())), c);
    // .add(D.neg()) ≡ .add(r0.w.mul(tw.neg()))
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(b.neg()).add(c), a.add(r0.y.mul(ty.neg())).add(c),
        d.neg(), r0.w.mul(tw.neg()),
    );
    // A.add(B.neg()).add(C).add(D.neg()) ≡ dot(r0, cv)

    // Final chain: det ≡ A.add(B.neg()).add(C).add(D.neg()) ≡ dot
    T::axiom_eqv_transitive(
        det(m),
        a.add(b.neg()).add(c).add(d.neg()),
        dot(r0, cofactor_vec(r1, r2, r3)),
    );
}

/// Helper: 0 - 0 + 0 - 0 ≡ 0
pub proof fn lemma_zero_alt_sum<T: Ring>()
    ensures
        T::zero().sub(T::zero()).add(T::zero()).sub(T::zero()).eqv(T::zero()),
{
    let z = T::zero();
    // sub_is_add_neg: z.sub(z) ≡ z.add(z.neg())
    T::axiom_sub_is_add_neg(z, z);
    // neg_zero: z.neg() ≡ z
    additive_group_lemmas::lemma_neg_zero::<T>();
    // z.add(z.neg()) ≡ z.add(z)
    additive_group_lemmas::lemma_add_congruence_right::<T>(z, z.neg(), z);
    // z.add(z) ≡ z
    T::axiom_add_zero_right(z);
    // Chain: z.sub(z) ≡ z.add(z.neg()) ≡ z.add(z) ≡ z
    T::axiom_eqv_transitive(z.sub(z), z.add(z.neg()), z.add(z));
    T::axiom_eqv_transitive(z.sub(z), z.add(z), z);

    // z.sub(z).add(z) ≡ z.add(z) ≡ z
    T::axiom_add_congruence_left(z.sub(z), z, z);
    T::axiom_eqv_transitive(z.sub(z).add(z), z.add(z), z);

    // z.sub(z).add(z).sub(z): use sub_is_add_neg again
    let s2 = z.sub(z).add(z);
    T::axiom_sub_is_add_neg(s2, z);
    // s2.sub(z) ≡ s2.add(z.neg())
    // s2 ≡ z and z.neg() ≡ z, so s2.add(z.neg()) ≡ z.add(z) ≡ z
    additive_group_lemmas::lemma_add_congruence::<T>(s2, z, z.neg(), z);
    T::axiom_eqv_transitive(s2.add(z.neg()), z.add(z), z);
    // Chain: s2.sub(z) ≡ s2.add(z.neg()) ≡ z
    T::axiom_eqv_transitive(s2.sub(z), s2.add(z.neg()), z);
}

/// Helper: given all four cofactors ≡ 0, det ≡ 0.
pub proof fn lemma_det_from_zero_cofactors<T: Ring>(r0: Vec4<T>, r1: Vec4<T>, r2: Vec4<T>, r3: Vec4<T>,
    tx: T, ty: T, tz: T, tw: T)
    requires
        tx.eqv(triple(drop_x(r1), drop_x(r2), drop_x(r3))),
        ty.eqv(triple(drop_y(r1), drop_y(r2), drop_y(r3))),
        tz.eqv(triple(drop_z(r1), drop_z(r2), drop_z(r3))),
        tw.eqv(triple(drop_w(r1), drop_w(r2), drop_w(r3))),
        tx.eqv(T::zero()),
        ty.eqv(T::zero()),
        tz.eqv(T::zero()),
        tw.eqv(T::zero()),
    ensures
        det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: r3 }).eqv(T::zero()),
{
    // Each cofactor ≡ 0 via transitivity through tx/ty/tz/tw
    T::axiom_eqv_symmetric(tx, triple(drop_x(r1), drop_x(r2), drop_x(r3)));
    T::axiom_eqv_transitive(triple(drop_x(r1), drop_x(r2), drop_x(r3)), tx, T::zero());
    T::axiom_eqv_symmetric(ty, triple(drop_y(r1), drop_y(r2), drop_y(r3)));
    T::axiom_eqv_transitive(triple(drop_y(r1), drop_y(r2), drop_y(r3)), ty, T::zero());
    T::axiom_eqv_symmetric(tz, triple(drop_z(r1), drop_z(r2), drop_z(r3)));
    T::axiom_eqv_transitive(triple(drop_z(r1), drop_z(r2), drop_z(r3)), tz, T::zero());
    T::axiom_eqv_symmetric(tw, triple(drop_w(r1), drop_w(r2), drop_w(r3)));
    T::axiom_eqv_transitive(triple(drop_w(r1), drop_w(r2), drop_w(r3)), tw, T::zero());

    // r0.k * cofactor ≡ r0.k * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(r0.x, triple(drop_x(r1), drop_x(r2), drop_x(r3)), T::zero());
    T::axiom_mul_zero_right(r0.x);
    T::axiom_eqv_transitive(r0.x.mul(triple(drop_x(r1), drop_x(r2), drop_x(r3))), r0.x.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(r0.y, triple(drop_y(r1), drop_y(r2), drop_y(r3)), T::zero());
    T::axiom_mul_zero_right(r0.y);
    T::axiom_eqv_transitive(r0.y.mul(triple(drop_y(r1), drop_y(r2), drop_y(r3))), r0.y.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(r0.z, triple(drop_z(r1), drop_z(r2), drop_z(r3)), T::zero());
    T::axiom_mul_zero_right(r0.z);
    T::axiom_eqv_transitive(r0.z.mul(triple(drop_z(r1), drop_z(r2), drop_z(r3))), r0.z.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(r0.w, triple(drop_w(r1), drop_w(r2), drop_w(r3)), T::zero());
    T::axiom_mul_zero_right(r0.w);
    T::axiom_eqv_transitive(r0.w.mul(triple(drop_w(r1), drop_w(r2), drop_w(r3))), r0.w.mul(T::zero()), T::zero());

    // det = a - b + c - d where a,b,c,d all ≡ 0
    let a = r0.x.mul(triple(drop_x(r1), drop_x(r2), drop_x(r3)));
    let b = r0.y.mul(triple(drop_y(r1), drop_y(r2), drop_y(r3)));
    let c = r0.z.mul(triple(drop_z(r1), drop_z(r2), drop_z(r3)));
    let d = r0.w.mul(triple(drop_w(r1), drop_w(r2), drop_w(r3)));

    additive_group_lemmas::lemma_sub_congruence(a, T::zero(), b, T::zero());
    additive_group_lemmas::lemma_add_congruence::<T>(a.sub(b), T::zero().sub(T::zero()), c, T::zero());
    additive_group_lemmas::lemma_sub_congruence(a.sub(b).add(c), T::zero().sub(T::zero()).add(T::zero()), d, T::zero());

    lemma_zero_alt_sum::<T>();
    T::axiom_eqv_transitive(
        a.sub(b).add(c).sub(d),
        T::zero().sub(T::zero()).add(T::zero()).sub(T::zero()),
        T::zero(),
    );
}

/// Helper: -(a - b + c - d) ≡ (-a) - (-b) + (-c) - (-d).
/// Strategy: convert sub→add(neg) on both sides, then use neg_add decomposition.
pub proof fn lemma_negate_alt_sum_4<T: Ring>(a: T, b: T, c: T, d: T)
    ensures
        a.sub(b).add(c).sub(d).neg().eqv(
            a.neg().sub(b.neg()).add(c.neg()).sub(d.neg())
        ),
{
    let s = a.sub(b).add(c).sub(d);
    let t = a.neg().sub(b.neg()).add(c.neg()).sub(d.neg());

    // === Convert s to add form ===
    // s = a.sub(b).add(c).sub(d)
    // s' = a.add(b.neg()).add(c).add(d.neg())
    T::axiom_sub_is_add_neg(a, b);
    T::axiom_add_congruence_left(a.sub(b), a.add(b.neg()), c);
    T::axiom_sub_is_add_neg(a.sub(b).add(c), d);
    T::axiom_add_congruence_left(a.sub(b).add(c), a.add(b.neg()).add(c), d.neg());
    T::axiom_eqv_transitive(s, a.sub(b).add(c).add(d.neg()), a.add(b.neg()).add(c).add(d.neg()));
    // s ≡ s' where s' = a.add(b.neg()).add(c).add(d.neg())
    let sp = a.add(b.neg()).add(c).add(d.neg());

    // neg_congruence: s ≡ s' → s.neg() ≡ s'.neg()
    T::axiom_neg_congruence(s, sp);
    // s.neg() ≡ sp.neg()

    // === Decompose neg(s') using neg_add ===
    // sp = ((a + b.neg()) + c) + d.neg()
    // neg(sp) ≡ neg((a+b.neg())+c) + neg(d.neg())  [neg_add]
    additive_group_lemmas::lemma_neg_add(a.add(b.neg()).add(c), d.neg());
    // neg((a+b.neg())+c) ≡ neg(a+b.neg()) + neg(c)  [neg_add]
    additive_group_lemmas::lemma_neg_add(a.add(b.neg()), c);
    // neg(a+b.neg()) ≡ neg(a) + neg(b.neg())  [neg_add]
    additive_group_lemmas::lemma_neg_add(a, b.neg());

    // neg(b.neg()) ≡ b, neg(d.neg()) ≡ d
    additive_group_lemmas::lemma_neg_involution(b);
    additive_group_lemmas::lemma_neg_involution(d);

    // Chain: neg(a+b.neg()) ≡ a.neg() + b.neg().neg() ≡ a.neg() + b
    additive_group_lemmas::lemma_add_congruence_right::<T>(a.neg(), b.neg().neg(), b);
    T::axiom_eqv_transitive(a.add(b.neg()).neg(), a.neg().add(b.neg().neg()), a.neg().add(b));

    // neg((a+b.neg())+c) ≡ neg(a+b.neg()) + c.neg() ≡ (a.neg()+b) + c.neg()
    T::axiom_add_congruence_left(a.add(b.neg()).neg(), a.neg().add(b), c.neg());
    T::axiom_eqv_transitive(
        a.add(b.neg()).add(c).neg(),
        a.add(b.neg()).neg().add(c.neg()),
        a.neg().add(b).add(c.neg()),
    );

    // neg(sp) ≡ neg((a+b.neg())+c) + neg(d.neg()) ≡ (a.neg()+b+c.neg()) + d
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(b.neg()).add(c).neg(), a.neg().add(b).add(c.neg()),
        d.neg().neg(), d,
    );
    T::axiom_eqv_transitive(
        sp.neg(),
        a.add(b.neg()).add(c).neg().add(d.neg().neg()),
        a.neg().add(b).add(c.neg()).add(d),
    );
    // sp.neg() ≡ a.neg().add(b).add(c.neg()).add(d)  =: u

    // s.neg() ≡ sp.neg() ≡ u
    let u = a.neg().add(b).add(c.neg()).add(d);
    T::axiom_eqv_transitive(s.neg(), sp.neg(), u);

    // === Convert t to add form ===
    // t = a.neg().sub(b.neg()).add(c.neg()).sub(d.neg())
    // t' = a.neg().add(b.neg().neg()).add(c.neg()).add(d.neg().neg())
    T::axiom_sub_is_add_neg(a.neg(), b.neg());
    T::axiom_add_congruence_left(a.neg().sub(b.neg()), a.neg().add(b.neg().neg()), c.neg());
    T::axiom_sub_is_add_neg(a.neg().sub(b.neg()).add(c.neg()), d.neg());
    T::axiom_add_congruence_left(a.neg().sub(b.neg()).add(c.neg()), a.neg().add(b.neg().neg()).add(c.neg()), d.neg().neg());
    T::axiom_eqv_transitive(
        t,
        a.neg().sub(b.neg()).add(c.neg()).add(d.neg().neg()),
        a.neg().add(b.neg().neg()).add(c.neg()).add(d.neg().neg()),
    );
    // t ≡ t' = a.neg().add(b.neg().neg()).add(c.neg()).add(d.neg().neg())

    // Simplify t' → u using neg_involution: b.neg().neg() ≡ b, d.neg().neg() ≡ d
    additive_group_lemmas::lemma_add_congruence_right::<T>(a.neg(), b.neg().neg(), b);
    T::axiom_add_congruence_left(a.neg().add(b.neg().neg()), a.neg().add(b), c.neg());
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.neg().add(b.neg().neg()).add(c.neg()), a.neg().add(b).add(c.neg()),
        d.neg().neg(), d,
    );
    // t' ≡ u
    T::axiom_eqv_transitive(
        t,
        a.neg().add(b.neg().neg()).add(c.neg()).add(d.neg().neg()),
        u,
    );
    // t ≡ u

    // Final: s.neg() ≡ u, t ≡ u → s.neg() ≡ t
    T::axiom_eqv_symmetric(t, u);
    T::axiom_eqv_transitive(s.neg(), u, t);
}

/// Helper: if a ≡ b.neg(), then b ≡ a.neg().
pub proof fn lemma_flip_neg_eqv<T: Ring>(a: T, b: T)
    requires a.eqv(b.neg())
    ensures b.eqv(a.neg())
{
    T::axiom_neg_congruence(a, b.neg());
    // a.neg() ≡ b.neg().neg()
    additive_group_lemmas::lemma_neg_involution(b);
    // b.neg().neg() ≡ b
    T::axiom_eqv_transitive(a.neg(), b.neg().neg(), b);
    // a.neg() ≡ b
    T::axiom_eqv_symmetric(a.neg(), b);
    // b ≡ a.neg()
}

/// Swapping rows 1 and 2 negates the determinant.
pub proof fn lemma_det_swap_rows_12<T: Ring>(m: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: m.row0, row1: m.row2, row2: m.row1, row3: m.row3 }).eqv(
            det(m).neg()
        ),
{
    let r0 = m.row0; let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;
    let tx = triple(drop_x(r1), drop_x(r2), drop_x(r3));
    let ty = triple(drop_y(r1), drop_y(r2), drop_y(r3));
    let tz = triple(drop_z(r1), drop_z(r2), drop_z(r3));
    let tw = triple(drop_w(r1), drop_w(r2), drop_w(r3));

    // swap_12 gives orig.eqv(swapped.neg()); flip to get swapped.eqv(orig.neg())
    lemma_triple_swap_12(drop_x(r1), drop_x(r2), drop_x(r3));
    lemma_flip_neg_eqv(tx, triple(drop_x(r2), drop_x(r1), drop_x(r3)));
    lemma_triple_swap_12(drop_y(r1), drop_y(r2), drop_y(r3));
    lemma_flip_neg_eqv(ty, triple(drop_y(r2), drop_y(r1), drop_y(r3)));
    lemma_triple_swap_12(drop_z(r1), drop_z(r2), drop_z(r3));
    lemma_flip_neg_eqv(tz, triple(drop_z(r2), drop_z(r1), drop_z(r3)));
    lemma_triple_swap_12(drop_w(r1), drop_w(r2), drop_w(r3));
    lemma_flip_neg_eqv(tw, triple(drop_w(r2), drop_w(r1), drop_w(r3)));
    // Now: triple(swapped_k).eqv(tk.neg()) for each k

    // r0.k * swapped_k ≡ r0.k * tk.neg() ≡ (r0.k * tk).neg()
    ring_lemmas::lemma_mul_neg_right(r0.x, tx);
    ring_lemmas::lemma_mul_congruence_right::<T>(
        r0.x, triple(drop_x(r2), drop_x(r1), drop_x(r3)), tx.neg(),
    );
    T::axiom_eqv_transitive(
        r0.x.mul(triple(drop_x(r2), drop_x(r1), drop_x(r3))),
        r0.x.mul(tx.neg()), r0.x.mul(tx).neg(),
    );

    ring_lemmas::lemma_mul_neg_right(r0.y, ty);
    ring_lemmas::lemma_mul_congruence_right::<T>(
        r0.y, triple(drop_y(r2), drop_y(r1), drop_y(r3)), ty.neg(),
    );
    T::axiom_eqv_transitive(
        r0.y.mul(triple(drop_y(r2), drop_y(r1), drop_y(r3))),
        r0.y.mul(ty.neg()), r0.y.mul(ty).neg(),
    );

    ring_lemmas::lemma_mul_neg_right(r0.z, tz);
    ring_lemmas::lemma_mul_congruence_right::<T>(
        r0.z, triple(drop_z(r2), drop_z(r1), drop_z(r3)), tz.neg(),
    );
    T::axiom_eqv_transitive(
        r0.z.mul(triple(drop_z(r2), drop_z(r1), drop_z(r3))),
        r0.z.mul(tz.neg()), r0.z.mul(tz).neg(),
    );

    ring_lemmas::lemma_mul_neg_right(r0.w, tw);
    ring_lemmas::lemma_mul_congruence_right::<T>(
        r0.w, triple(drop_w(r2), drop_w(r1), drop_w(r3)), tw.neg(),
    );
    T::axiom_eqv_transitive(
        r0.w.mul(triple(drop_w(r2), drop_w(r1), drop_w(r3))),
        r0.w.mul(tw.neg()), r0.w.mul(tw).neg(),
    );

    let a = r0.x.mul(tx); let b = r0.y.mul(ty); let c = r0.z.mul(tz); let d = r0.w.mul(tw);
    let a2 = r0.x.mul(triple(drop_x(r2), drop_x(r1), drop_x(r3)));
    let b2 = r0.y.mul(triple(drop_y(r2), drop_y(r1), drop_y(r3)));
    let c2 = r0.z.mul(triple(drop_z(r2), drop_z(r1), drop_z(r3)));
    let d2 = r0.w.mul(triple(drop_w(r2), drop_w(r1), drop_w(r3)));

    // a2 ≡ a.neg(), b2 ≡ b.neg(), c2 ≡ c.neg(), d2 ≡ d.neg()
    // det(swapped) = a2 - b2 + c2 - d2 ≡ a.neg() - b.neg() + c.neg() - d.neg()
    additive_group_lemmas::lemma_sub_congruence(a2, a.neg(), b2, b.neg());
    additive_group_lemmas::lemma_add_congruence::<T>(a2.sub(b2), a.neg().sub(b.neg()), c2, c.neg());
    additive_group_lemmas::lemma_sub_congruence(a2.sub(b2).add(c2), a.neg().sub(b.neg()).add(c.neg()), d2, d.neg());

    // (-a) - (-b) + (-c) - (-d) ≡ -(a - b + c - d)
    lemma_negate_alt_sum_4(a, b, c, d);
    T::axiom_eqv_symmetric(a.sub(b).add(c).sub(d).neg(), a.neg().sub(b.neg()).add(c.neg()).sub(d.neg()));

    T::axiom_eqv_transitive(
        a2.sub(b2).add(c2).sub(d2),
        a.neg().sub(b.neg()).add(c.neg()).sub(d.neg()),
        a.sub(b).add(c).sub(d).neg(),
    );
}

/// Swapping rows 2 and 3 negates the determinant.
pub proof fn lemma_det_swap_rows_23<T: Ring>(m: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: m.row0, row1: m.row1, row2: m.row3, row3: m.row2 }).eqv(
            det(m).neg()
        ),
{
    let r0 = m.row0; let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;
    lemma_triple_swap_23(drop_x(r1), drop_x(r2), drop_x(r3));
    lemma_triple_swap_23(drop_y(r1), drop_y(r2), drop_y(r3));
    lemma_triple_swap_23(drop_z(r1), drop_z(r2), drop_z(r3));
    lemma_triple_swap_23(drop_w(r1), drop_w(r2), drop_w(r3));

    let tx = triple(drop_x(r1), drop_x(r2), drop_x(r3));
    let ty = triple(drop_y(r1), drop_y(r2), drop_y(r3));
    let tz = triple(drop_z(r1), drop_z(r2), drop_z(r3));
    let tw = triple(drop_w(r1), drop_w(r2), drop_w(r3));

    ring_lemmas::lemma_mul_neg_right(r0.x, tx);
    ring_lemmas::lemma_mul_neg_right(r0.y, ty);
    ring_lemmas::lemma_mul_neg_right(r0.z, tz);
    ring_lemmas::lemma_mul_neg_right(r0.w, tw);

    ring_lemmas::lemma_mul_congruence_right::<T>(
        r0.x, triple(drop_x(r1), drop_x(r3), drop_x(r2)),
        triple(drop_x(r1), drop_x(r2), drop_x(r3)).neg(),
    );
    T::axiom_eqv_transitive(
        r0.x.mul(triple(drop_x(r1), drop_x(r3), drop_x(r2))),
        r0.x.mul(triple(drop_x(r1), drop_x(r2), drop_x(r3)).neg()),
        r0.x.mul(tx).neg(),
    );

    ring_lemmas::lemma_mul_congruence_right::<T>(
        r0.y, triple(drop_y(r1), drop_y(r3), drop_y(r2)),
        triple(drop_y(r1), drop_y(r2), drop_y(r3)).neg(),
    );
    T::axiom_eqv_transitive(
        r0.y.mul(triple(drop_y(r1), drop_y(r3), drop_y(r2))),
        r0.y.mul(triple(drop_y(r1), drop_y(r2), drop_y(r3)).neg()),
        r0.y.mul(ty).neg(),
    );

    ring_lemmas::lemma_mul_congruence_right::<T>(
        r0.z, triple(drop_z(r1), drop_z(r3), drop_z(r2)),
        triple(drop_z(r1), drop_z(r2), drop_z(r3)).neg(),
    );
    T::axiom_eqv_transitive(
        r0.z.mul(triple(drop_z(r1), drop_z(r3), drop_z(r2))),
        r0.z.mul(triple(drop_z(r1), drop_z(r2), drop_z(r3)).neg()),
        r0.z.mul(tz).neg(),
    );

    ring_lemmas::lemma_mul_congruence_right::<T>(
        r0.w, triple(drop_w(r1), drop_w(r3), drop_w(r2)),
        triple(drop_w(r1), drop_w(r2), drop_w(r3)).neg(),
    );
    T::axiom_eqv_transitive(
        r0.w.mul(triple(drop_w(r1), drop_w(r3), drop_w(r2))),
        r0.w.mul(triple(drop_w(r1), drop_w(r2), drop_w(r3)).neg()),
        r0.w.mul(tw).neg(),
    );

    let a = r0.x.mul(tx); let b = r0.y.mul(ty); let c = r0.z.mul(tz); let d = r0.w.mul(tw);
    let a2 = r0.x.mul(triple(drop_x(r1), drop_x(r3), drop_x(r2)));
    let b2 = r0.y.mul(triple(drop_y(r1), drop_y(r3), drop_y(r2)));
    let c2 = r0.z.mul(triple(drop_z(r1), drop_z(r3), drop_z(r2)));
    let d2 = r0.w.mul(triple(drop_w(r1), drop_w(r3), drop_w(r2)));

    additive_group_lemmas::lemma_sub_congruence(a2, a.neg(), b2, b.neg());
    additive_group_lemmas::lemma_add_congruence::<T>(a2.sub(b2), a.neg().sub(b.neg()), c2, c.neg());
    additive_group_lemmas::lemma_sub_congruence(a2.sub(b2).add(c2), a.neg().sub(b.neg()).add(c.neg()), d2, d.neg());

    lemma_negate_alt_sum_4(a, b, c, d);
    T::axiom_eqv_symmetric(a.sub(b).add(c).sub(d).neg(), a.neg().sub(b.neg()).add(c.neg()).sub(d.neg()));

    T::axiom_eqv_transitive(
        a2.sub(b2).add(c2).sub(d2),
        a.neg().sub(b.neg()).add(c.neg()).sub(d.neg()),
        a.sub(b).add(c).sub(d).neg(),
    );
}

/// If rows 1 and 2 are equal, det is zero.
pub proof fn lemma_det_zero_repeated_row_12<T: Ring>(r0: Vec4<T>, a: Vec4<T>, b: Vec4<T>)
    ensures
        det(Mat4x4 { row0: r0, row1: a, row2: a, row3: b }).eqv(T::zero()),
{
    lemma_triple_self_zero_12(drop_x(a), drop_x(b));
    lemma_triple_self_zero_12(drop_y(a), drop_y(b));
    lemma_triple_self_zero_12(drop_z(a), drop_z(b));
    lemma_triple_self_zero_12(drop_w(a), drop_w(b));
    let tx = triple(drop_x(a), drop_x(a), drop_x(b));
    let ty = triple(drop_y(a), drop_y(a), drop_y(b));
    let tz = triple(drop_z(a), drop_z(a), drop_z(b));
    let tw = triple(drop_w(a), drop_w(a), drop_w(b));
    T::axiom_eqv_reflexive(tx);
    T::axiom_eqv_reflexive(ty);
    T::axiom_eqv_reflexive(tz);
    T::axiom_eqv_reflexive(tw);
    lemma_det_from_zero_cofactors(r0, a, a, b, tx, ty, tz, tw);
}

/// If rows 2 and 3 are equal, det is zero.
pub proof fn lemma_det_zero_repeated_row_23<T: Ring>(r0: Vec4<T>, a: Vec4<T>, b: Vec4<T>)
    ensures
        det(Mat4x4 { row0: r0, row1: a, row2: b, row3: b }).eqv(T::zero()),
{
    lemma_triple_self_zero_23(drop_x(a), drop_x(b));
    lemma_triple_self_zero_23(drop_y(a), drop_y(b));
    lemma_triple_self_zero_23(drop_z(a), drop_z(b));
    lemma_triple_self_zero_23(drop_w(a), drop_w(b));
    let tx = triple(drop_x(a), drop_x(b), drop_x(b));
    let ty = triple(drop_y(a), drop_y(b), drop_y(b));
    let tz = triple(drop_z(a), drop_z(b), drop_z(b));
    let tw = triple(drop_w(a), drop_w(b), drop_w(b));
    T::axiom_eqv_reflexive(tx);
    T::axiom_eqv_reflexive(ty);
    T::axiom_eqv_reflexive(tz);
    T::axiom_eqv_reflexive(tw);
    lemma_det_from_zero_cofactors(r0, a, b, b, tx, ty, tz, tw);
}

/// Determinant is linear in the first row.
pub proof fn lemma_det_linear_first_row<T: Ring>(a: Vec4<T>, b: Vec4<T>,
    r1: Vec4<T>, r2: Vec4<T>, r3: Vec4<T>)
    ensures
        det(Mat4x4 { row0: a.add(b), row1: r1, row2: r2, row3: r3 }).eqv(
            det(Mat4x4 { row0: a, row1: r1, row2: r2, row3: r3 }).add(
                det(Mat4x4 { row0: b, row1: r1, row2: r2, row3: r3 })
            )
        ),
{
    let cv = cofactor_vec(r1, r2, r3);
    lemma_det_as_dot(Mat4x4 { row0: a.add(b), row1: r1, row2: r2, row3: r3 });
    lemma_det_as_dot(Mat4x4 { row0: a, row1: r1, row2: r2, row3: r3 });
    lemma_det_as_dot(Mat4x4 { row0: b, row1: r1, row2: r2, row3: r3 });

    // dot(a+b, cv) ≡ dot(a, cv) + dot(b, cv)
    crate::vec4::ops::lemma_dot_distributes_left(a, b, cv);

    // det([a+b,...]) ≡ dot(a+b, cv) ≡ dot(a,cv) + dot(b,cv)
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: a.add(b), row1: r1, row2: r2, row3: r3 }),
        dot(a.add(b), cv),
        dot(a, cv).add(dot(b, cv)),
    );

    // dot(a,cv) ≡ det([a,...]) and dot(b,cv) ≡ det([b,...])
    T::axiom_eqv_symmetric(
        det(Mat4x4 { row0: a, row1: r1, row2: r2, row3: r3 }),
        dot(a, cv),
    );
    T::axiom_eqv_symmetric(
        det(Mat4x4 { row0: b, row1: r1, row2: r2, row3: r3 }),
        dot(b, cv),
    );

    additive_group_lemmas::lemma_add_congruence::<T>(
        dot(a, cv),
        det(Mat4x4 { row0: a, row1: r1, row2: r2, row3: r3 }),
        dot(b, cv),
        det(Mat4x4 { row0: b, row1: r1, row2: r2, row3: r3 }),
    );

    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: a.add(b), row1: r1, row2: r2, row3: r3 }),
        dot(a, cv).add(dot(b, cv)),
        det(Mat4x4 { row0: a, row1: r1, row2: r2, row3: r3 }).add(
            det(Mat4x4 { row0: b, row1: r1, row2: r2, row3: r3 })
        ),
    );
}

// ---------------------------------------------------------------------------
// Phase 2: Additional det properties
// ---------------------------------------------------------------------------

/// det(scale(s, r0), r1, r2, r3) ≡ s * det(r0, r1, r2, r3)
pub proof fn lemma_det_scale_first_row<T: Ring>(s: T, r0: Vec4<T>,
    r1: Vec4<T>, r2: Vec4<T>, r3: Vec4<T>)
    ensures
        det(Mat4x4 { row0: scale(s, r0), row1: r1, row2: r2, row3: r3 }).eqv(
            s.mul(det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: r3 }))
        ),
{
    let cv = cofactor_vec(r1, r2, r3);
    let m_scaled = Mat4x4 { row0: scale(s, r0), row1: r1, row2: r2, row3: r3 };
    let m_orig = Mat4x4 { row0: r0, row1: r1, row2: r2, row3: r3 };

    // det(m_scaled) ≡ dot(scale(s, r0), cv)
    lemma_det_as_dot(m_scaled);

    // dot(scale(s, r0), cv) ≡ s * dot(r0, cv)
    crate::vec4::ops::lemma_dot_scale_left(s, r0, cv);

    // det(m_scaled) ≡ s * dot(r0, cv)
    T::axiom_eqv_transitive(det(m_scaled), dot(scale(s, r0), cv), s.mul(dot(r0, cv)));

    // det(m_orig) ≡ dot(r0, cv)
    lemma_det_as_dot(m_orig);

    // s * dot(r0, cv) ≡ s * det(m_orig)
    T::axiom_eqv_symmetric(det(m_orig), dot(r0, cv));
    ring_lemmas::lemma_mul_congruence_right::<T>(s, dot(r0, cv), det(m_orig));

    // chain: det(m_scaled) ≡ s * dot(r0, cv) ≡ s * det(m_orig)
    T::axiom_eqv_transitive(det(m_scaled), s.mul(dot(r0, cv)), s.mul(det(m_orig)));
}

/// If rows 1 and 3 are equal, det is zero.
pub proof fn lemma_det_zero_repeated_row_13<T: Ring>(r0: Vec4<T>, a: Vec4<T>, b: Vec4<T>)
    ensures
        det(Mat4x4 { row0: r0, row1: a, row2: b, row3: a }).eqv(T::zero()),
{
    // swap_23 on {r0, a, b, a}: det(r0, a, a, b) ≡ -det(r0, a, b, a)
    let m = Mat4x4 { row0: r0, row1: a, row2: b, row3: a };
    lemma_det_swap_rows_23(m);
    // det(r0, a, a, b) ≡ det(r0, a, b, a).neg()

    // det(r0, a, a, b) ≡ 0
    lemma_det_zero_repeated_row_12(r0, a, b);

    // det(r0, a, b, a).neg() ≡ det(r0, a, a, b) ≡ 0
    T::axiom_eqv_symmetric(
        det(Mat4x4 { row0: r0, row1: a, row2: a, row3: b }),
        det(m).neg(),
    );
    T::axiom_eqv_transitive(det(m).neg(),
        det(Mat4x4 { row0: r0, row1: a, row2: a, row3: b }),
        T::zero(),
    );

    // det(m).neg() ≡ 0 → det(m) ≡ 0
    T::axiom_neg_congruence(det(m).neg(), T::zero());
    additive_group_lemmas::lemma_neg_involution(det(m));
    T::axiom_eqv_symmetric(det(m).neg().neg(), det(m));
    T::axiom_eqv_transitive(det(m), det(m).neg().neg(), T::zero().neg());
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(det(m), T::zero().neg(), T::zero());
}

/// Swapping rows 1 and 3 negates the determinant.
/// Proof: compose swap_12, swap_23, swap_12 (three adjacent swaps = one transposition).
pub proof fn lemma_det_swap_rows_13<T: Ring>(m: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: m.row0, row1: m.row3, row2: m.row2, row3: m.row1 }).eqv(
            det(m).neg()
        ),
{
    let r0 = m.row0; let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;

    // Step 1: swap_12 on m: det(r0, r2, r1, r3) ≡ det(m).neg()
    lemma_det_swap_rows_12(m);
    let m2 = Mat4x4 { row0: r0, row1: r2, row2: r1, row3: r3 };

    // Step 2: swap_23 on m2: det(r0, r2, r3, r1) ≡ det(m2).neg()
    lemma_det_swap_rows_23(m2);
    let m3 = Mat4x4 { row0: r0, row1: r2, row2: r3, row3: r1 };

    // Chain: det(m2).neg() ≡ det(m).neg().neg() ≡ det(m)
    T::axiom_neg_congruence(det(m2), det(m).neg());
    additive_group_lemmas::lemma_neg_involution(det(m));
    T::axiom_eqv_transitive(det(m2).neg(), det(m).neg().neg(), det(m));

    // det(m3) ≡ det(m2).neg() ≡ det(m)
    T::axiom_eqv_transitive(det(m3), det(m2).neg(), det(m));

    // Step 3: swap_12 on m3: det(r0, r3, r2, r1) ≡ det(m3).neg()
    lemma_det_swap_rows_12(m3);

    // det(m3).neg() ≡ det(m).neg()
    T::axiom_neg_congruence(det(m3), det(m));

    // Final chain: det(r0, r3, r2, r1) ≡ det(m3).neg() ≡ det(m).neg()
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: r0, row1: r3, row2: r2, row3: r1 }),
        det(m3).neg(),
        det(m).neg(),
    );
}

// ---------------------------------------------------------------------------
// Cofactor vec linearity/scaling/negation in first argument
// ---------------------------------------------------------------------------

/// cofactor_vec(a + b, c, d) ≡ cofactor_vec(a, c, d) + cofactor_vec(b, c, d)
pub proof fn lemma_cofactor_vec_linear_first<T: Ring>(
    a: Vec4<T>, b: Vec4<T>, c: Vec4<T>, d: Vec4<T>,
)
    ensures
        cofactor_vec(a.add(b), c, d).eqv(
            cofactor_vec(a, c, d).add(cofactor_vec(b, c, d))
        ),
{
    // x component: triple_linear_first (structural drop_k(a+b) == drop_k(a) + drop_k(b))
    lemma_triple_linear_first(drop_x(a), drop_x(b), drop_x(c), drop_x(d));
    // z component: same
    lemma_triple_linear_first(drop_z(a), drop_z(b), drop_z(c), drop_z(d));

    // y component: triple_linear_first + neg_add
    lemma_triple_linear_first(drop_y(a), drop_y(b), drop_y(c), drop_y(d));
    // (T_a + T_b).neg() ≡ T_a.neg() + T_b.neg()
    let ty_a = triple(drop_y(a), drop_y(c), drop_y(d));
    let ty_b = triple(drop_y(b), drop_y(c), drop_y(d));
    T::axiom_neg_congruence(
        triple(drop_y(a.add(b)), drop_y(c), drop_y(d)),
        ty_a.add(ty_b),
    );
    additive_group_lemmas::lemma_neg_add(ty_a, ty_b);
    T::axiom_eqv_transitive(
        triple(drop_y(a.add(b)), drop_y(c), drop_y(d)).neg(),
        ty_a.add(ty_b).neg(),
        ty_a.neg().add(ty_b.neg()),
    );

    // w component: same pattern as y
    lemma_triple_linear_first(drop_w(a), drop_w(b), drop_w(c), drop_w(d));
    let tw_a = triple(drop_w(a), drop_w(c), drop_w(d));
    let tw_b = triple(drop_w(b), drop_w(c), drop_w(d));
    T::axiom_neg_congruence(
        triple(drop_w(a.add(b)), drop_w(c), drop_w(d)),
        tw_a.add(tw_b),
    );
    additive_group_lemmas::lemma_neg_add(tw_a, tw_b);
    T::axiom_eqv_transitive(
        triple(drop_w(a.add(b)), drop_w(c), drop_w(d)).neg(),
        tw_a.add(tw_b).neg(),
        tw_a.neg().add(tw_b.neg()),
    );
}

/// cofactor_vec(scale(s, a), b, c) ≡ scale(s, cofactor_vec(a, b, c))
pub proof fn lemma_cofactor_vec_scale_first<T: Ring>(
    s: T, a: Vec4<T>, b: Vec4<T>, c: Vec4<T>,
)
    ensures
        cofactor_vec(scale(s, a), b, c).eqv(
            scale(s, cofactor_vec(a, b, c))
        ),
{
    // x component: triple_scale_first (structural drop_k(scale(s,a)) == scale(s, drop_k(a)))
    lemma_triple_scale_first(s, drop_x(a), drop_x(b), drop_x(c));
    // z component: same
    lemma_triple_scale_first(s, drop_z(a), drop_z(b), drop_z(c));

    // y component: triple_scale_first + s * (T.neg()) ≡ (s * T).neg()
    lemma_triple_scale_first(s, drop_y(a), drop_y(b), drop_y(c));
    let ty = triple(drop_y(a), drop_y(b), drop_y(c));
    // triple(scale(s, drop_y(a)), ...) ≡ s * ty
    // LHS.neg() ≡ (s * ty).neg()
    T::axiom_neg_congruence(
        triple(drop_y(scale(s, a)), drop_y(b), drop_y(c)),
        s.mul(ty),
    );
    // RHS: s * (ty.neg()) — need s * (-ty) ≡ -(s * ty)
    ring_lemmas::lemma_mul_neg_right(s, ty);
    // s * ty.neg() ≡ (s * ty).neg()
    T::axiom_eqv_symmetric(s.mul(ty).neg(), s.mul(ty.neg()));
    // chain: LHS.neg() ≡ (s*ty).neg() ≡ s * ty.neg()
    T::axiom_eqv_transitive(
        triple(drop_y(scale(s, a)), drop_y(b), drop_y(c)).neg(),
        s.mul(ty).neg(),
        s.mul(ty.neg()),
    );

    // w component: same pattern as y
    lemma_triple_scale_first(s, drop_w(a), drop_w(b), drop_w(c));
    let tw = triple(drop_w(a), drop_w(b), drop_w(c));
    T::axiom_neg_congruence(
        triple(drop_w(scale(s, a)), drop_w(b), drop_w(c)),
        s.mul(tw),
    );
    ring_lemmas::lemma_mul_neg_right(s, tw);
    T::axiom_eqv_symmetric(s.mul(tw).neg(), s.mul(tw.neg()));
    T::axiom_eqv_transitive(
        triple(drop_w(scale(s, a)), drop_w(b), drop_w(c)).neg(),
        s.mul(tw).neg(),
        s.mul(tw.neg()),
    );
}

/// cofactor_vec(a.neg(), b, c) ≡ cofactor_vec(a, b, c).neg()
pub proof fn lemma_cofactor_vec_neg_first<T: Ring>(
    a: Vec4<T>, b: Vec4<T>, c: Vec4<T>,
)
    ensures
        cofactor_vec(a.neg(), b, c).eqv(
            cofactor_vec(a, b, c).neg()
        ),
{
    // x: triple_neg_first
    lemma_triple_neg_first(drop_x(a), drop_x(b), drop_x(c));
    // z: triple_neg_first
    lemma_triple_neg_first(drop_z(a), drop_z(b), drop_z(c));

    // y: triple_neg_first + neg(neg(T)) ≡ T
    lemma_triple_neg_first(drop_y(a), drop_y(b), drop_y(c));
    let ty = triple(drop_y(a), drop_y(b), drop_y(c));
    // triple(drop_y(a).neg(), ...) ≡ ty.neg()
    // LHS.neg() ≡ ty.neg().neg() ≡ ty
    T::axiom_neg_congruence(
        triple(drop_y(a.neg()), drop_y(b), drop_y(c)),
        ty.neg(),
    );
    additive_group_lemmas::lemma_neg_involution(ty);
    T::axiom_eqv_transitive(
        triple(drop_y(a.neg()), drop_y(b), drop_y(c)).neg(),
        ty.neg().neg(),
        ty,
    );
    // RHS.y = cofactor_vec(a, b, c).neg().y = ty.neg().neg() ≡ ty
    // But wait: cofactor_vec(a,b,c).neg() = Vec4{..., y: ty.neg().neg(), ...}
    // And we showed LHS.y = triple(drop_y(a.neg()), ...).neg() ≡ ty
    // Need to show ty ≡ ty.neg().neg() → already have neg_involution: ty.neg().neg() ≡ ty
    // So LHS.y ≡ ty and RHS.y = ty.neg().neg(), need LHS.y ≡ RHS.y
    // ty ≡ ty.neg().neg() by symmetric of neg_involution
    T::axiom_eqv_symmetric(ty.neg().neg(), ty);
    T::axiom_eqv_transitive(
        triple(drop_y(a.neg()), drop_y(b), drop_y(c)).neg(),
        ty,
        ty.neg().neg(),
    );

    // w: same pattern as y
    lemma_triple_neg_first(drop_w(a), drop_w(b), drop_w(c));
    let tw = triple(drop_w(a), drop_w(b), drop_w(c));
    T::axiom_neg_congruence(
        triple(drop_w(a.neg()), drop_w(b), drop_w(c)),
        tw.neg(),
    );
    additive_group_lemmas::lemma_neg_involution(tw);
    T::axiom_eqv_transitive(
        triple(drop_w(a.neg()), drop_w(b), drop_w(c)).neg(),
        tw.neg().neg(),
        tw,
    );
    T::axiom_eqv_symmetric(tw.neg().neg(), tw);
    T::axiom_eqv_transitive(
        triple(drop_w(a.neg()), drop_w(b), drop_w(c)).neg(),
        tw,
        tw.neg().neg(),
    );
}

// ---------------------------------------------------------------------------
// Determinant linearity/scaling in the second row
// ---------------------------------------------------------------------------

/// det(r0, a + b, r2, r3) ≡ det(r0, a, r2, r3) + det(r0, b, r2, r3)
pub proof fn lemma_det_linear_second_row<T: Ring>(r0: Vec4<T>,
    a: Vec4<T>, b: Vec4<T>, r2: Vec4<T>, r3: Vec4<T>)
    ensures
        det(Mat4x4 { row0: r0, row1: a.add(b), row2: r2, row3: r3 }).eqv(
            det(Mat4x4 { row0: r0, row1: a, row2: r2, row3: r3 }).add(
                det(Mat4x4 { row0: r0, row1: b, row2: r2, row3: r3 })
            )
        ),
{
    let m_ab = Mat4x4 { row0: r0, row1: a.add(b), row2: r2, row3: r3 };
    let m_a = Mat4x4 { row0: r0, row1: a, row2: r2, row3: r3 };
    let m_b = Mat4x4 { row0: r0, row1: b, row2: r2, row3: r3 };
    let cv_ab = cofactor_vec(a.add(b), r2, r3);
    let cv_a = cofactor_vec(a, r2, r3);
    let cv_b = cofactor_vec(b, r2, r3);

    // det ≡ dot(r0, cv) for each
    lemma_det_as_dot(m_ab);
    lemma_det_as_dot(m_a);
    lemma_det_as_dot(m_b);

    // cv_ab ≡ cv_a + cv_b
    lemma_cofactor_vec_linear_first(a, b, r2, r3);

    // dot(r0, cv_ab) ≡ dot(r0, cv_a + cv_b)
    Vec4::axiom_eqv_reflexive(r0);
    crate::vec4::ops::lemma_dot_congruence(r0, r0, cv_ab, cv_a.add(cv_b));

    // dot(r0, cv_a + cv_b) ≡ dot(r0, cv_a) + dot(r0, cv_b)
    crate::vec4::ops::lemma_dot_distributes_right(r0, cv_a, cv_b);

    // Chain: det(m_ab) ≡ dot(r0, cv_ab) ≡ dot(r0, cv_a + cv_b) ≡ dot(r0, cv_a) + dot(r0, cv_b)
    T::axiom_eqv_transitive(det(m_ab), dot(r0, cv_ab), dot(r0, cv_a.add(cv_b)));
    T::axiom_eqv_transitive(det(m_ab), dot(r0, cv_a.add(cv_b)),
        dot(r0, cv_a).add(dot(r0, cv_b)));

    // dot(r0, cv_a) ≡ det(m_a), dot(r0, cv_b) ≡ det(m_b)
    T::axiom_eqv_symmetric(det(m_a), dot(r0, cv_a));
    T::axiom_eqv_symmetric(det(m_b), dot(r0, cv_b));
    additive_group_lemmas::lemma_add_congruence::<T>(
        dot(r0, cv_a), det(m_a), dot(r0, cv_b), det(m_b),
    );

    // Final chain
    T::axiom_eqv_transitive(det(m_ab),
        dot(r0, cv_a).add(dot(r0, cv_b)),
        det(m_a).add(det(m_b)));
}

/// det(r0, scale(s, r1), r2, r3) ≡ s * det(r0, r1, r2, r3)
pub proof fn lemma_det_scale_second_row<T: Ring>(s: T, r0: Vec4<T>,
    r1: Vec4<T>, r2: Vec4<T>, r3: Vec4<T>)
    ensures
        det(Mat4x4 { row0: r0, row1: scale(s, r1), row2: r2, row3: r3 }).eqv(
            s.mul(det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: r3 }))
        ),
{
    let m_s = Mat4x4 { row0: r0, row1: scale(s, r1), row2: r2, row3: r3 };
    let m = Mat4x4 { row0: r0, row1: r1, row2: r2, row3: r3 };
    let cv_s = cofactor_vec(scale(s, r1), r2, r3);
    let cv = cofactor_vec(r1, r2, r3);

    lemma_det_as_dot(m_s);
    lemma_det_as_dot(m);

    // cv_s ≡ scale(s, cv)
    lemma_cofactor_vec_scale_first(s, r1, r2, r3);

    // dot(r0, cv_s) ≡ dot(r0, scale(s, cv))
    Vec4::axiom_eqv_reflexive(r0);
    crate::vec4::ops::lemma_dot_congruence(r0, r0, cv_s, scale(s, cv));

    // dot(r0, scale(s, cv)) ≡ s * dot(r0, cv)
    crate::vec4::ops::lemma_dot_scale_right(s, r0, cv);

    // Chain: det(m_s) ≡ dot(r0, cv_s) ≡ dot(r0, scale(s, cv)) ≡ s * dot(r0, cv)
    T::axiom_eqv_transitive(det(m_s), dot(r0, cv_s), dot(r0, scale(s, cv)));
    T::axiom_eqv_transitive(det(m_s), dot(r0, scale(s, cv)), s.mul(dot(r0, cv)));

    // s * dot(r0, cv) ≡ s * det(m)
    T::axiom_eqv_symmetric(det(m), dot(r0, cv));
    ring_lemmas::lemma_mul_congruence_right::<T>(s, dot(r0, cv), det(m));
    T::axiom_eqv_transitive(det(m_s), s.mul(dot(r0, cv)), s.mul(det(m)));
}

} // verus!
