use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::field_lemmas;
use crate::vec3::Vec3;
use crate::vec3::ops::{dot, scale, cross, triple};
use super::Mat3x3;

verus! {

// ---------------------------------------------------------------------------
// Spec functions
// ---------------------------------------------------------------------------

pub open spec fn identity<T: Ring>() -> Mat3x3<T> {
    Mat3x3 {
        row0: Vec3 { x: T::one(), y: T::zero(), z: T::zero() },
        row1: Vec3 { x: T::zero(), y: T::one(), z: T::zero() },
        row2: Vec3 { x: T::zero(), y: T::zero(), z: T::one() },
    }
}

pub open spec fn mat_vec_mul<T: Ring>(m: Mat3x3<T>, v: Vec3<T>) -> Vec3<T> {
    Vec3 { x: dot(m.row0, v), y: dot(m.row1, v), z: dot(m.row2, v) }
}

pub open spec fn transpose<T: Ring>(m: Mat3x3<T>) -> Mat3x3<T> {
    Mat3x3 {
        row0: Vec3 { x: m.row0.x, y: m.row1.x, z: m.row2.x },
        row1: Vec3 { x: m.row0.y, y: m.row1.y, z: m.row2.y },
        row2: Vec3 { x: m.row0.z, y: m.row1.z, z: m.row2.z },
    }
}

pub open spec fn det<T: Ring>(m: Mat3x3<T>) -> T {
    triple(m.row0, m.row1, m.row2)
}

pub open spec fn mat_mul<T: Ring>(a: Mat3x3<T>, b: Mat3x3<T>) -> Mat3x3<T> {
    let bt = transpose(b);
    Mat3x3 {
        row0: Vec3 {
            x: dot(a.row0, bt.row0),
            y: dot(a.row0, bt.row1),
            z: dot(a.row0, bt.row2),
        },
        row1: Vec3 {
            x: dot(a.row1, bt.row0),
            y: dot(a.row1, bt.row1),
            z: dot(a.row1, bt.row2),
        },
        row2: Vec3 {
            x: dot(a.row2, bt.row0),
            y: dot(a.row2, bt.row1),
            z: dot(a.row2, bt.row2),
        },
    }
}

// ---------------------------------------------------------------------------
// Transpose
// ---------------------------------------------------------------------------

/// transpose(transpose(m)) ≡ m  (structurally identical, just needs reflexivity)
pub proof fn lemma_transpose_involution<T: Ring>(m: Mat3x3<T>)
    ensures
        transpose(transpose(m)).row0.eqv(m.row0),
        transpose(transpose(m)).row1.eqv(m.row1),
        transpose(transpose(m)).row2.eqv(m.row2),
{
    T::axiom_eqv_reflexive(m.row0.x);
    T::axiom_eqv_reflexive(m.row0.y);
    T::axiom_eqv_reflexive(m.row0.z);
    T::axiom_eqv_reflexive(m.row1.x);
    T::axiom_eqv_reflexive(m.row1.y);
    T::axiom_eqv_reflexive(m.row1.z);
    T::axiom_eqv_reflexive(m.row2.x);
    T::axiom_eqv_reflexive(m.row2.y);
    T::axiom_eqv_reflexive(m.row2.z);
}

// ---------------------------------------------------------------------------
// mat_vec_mul lemmas
// ---------------------------------------------------------------------------

/// mat_vec_mul(m, zero) ≡ zero
pub proof fn lemma_mat_vec_mul_zero<T: Ring>(m: Mat3x3<T>)
    ensures
        mat_vec_mul(m, Vec3 { x: T::zero(), y: T::zero(), z: T::zero() })
            .eqv(Vec3 { x: T::zero(), y: T::zero(), z: T::zero() }),
{
    let z = Vec3 { x: T::zero(), y: T::zero(), z: T::zero() };
    crate::vec3::ops::lemma_dot_zero_right(m.row0);
    crate::vec3::ops::lemma_dot_zero_right(m.row1);
    crate::vec3::ops::lemma_dot_zero_right(m.row2);
}

/// mat_vec_mul(m, a + b) ≡ mat_vec_mul(m, a) + mat_vec_mul(m, b)
pub proof fn lemma_mat_vec_mul_add<T: Ring>(m: Mat3x3<T>, a: Vec3<T>, b: Vec3<T>)
    ensures
        mat_vec_mul(m, a.add(b)).eqv(
            mat_vec_mul(m, a).add(mat_vec_mul(m, b))
        ),
{
    crate::vec3::ops::lemma_dot_distributes_right(m.row0, a, b);
    crate::vec3::ops::lemma_dot_distributes_right(m.row1, a, b);
    crate::vec3::ops::lemma_dot_distributes_right(m.row2, a, b);
}

/// mat_vec_mul(m, scale(s, v)) ≡ scale(s, mat_vec_mul(m, v))
pub proof fn lemma_mat_vec_mul_scale<T: Ring>(m: Mat3x3<T>, s: T, v: Vec3<T>)
    ensures
        mat_vec_mul(m, scale(s, v)).eqv(
            scale(s, mat_vec_mul(m, v))
        ),
{
    crate::vec3::ops::lemma_dot_scale_right(s, m.row0, v);
    crate::vec3::ops::lemma_dot_scale_right(s, m.row1, v);
    crate::vec3::ops::lemma_dot_scale_right(s, m.row2, v);
}

/// dot of unit vector e_i with v ≡ v's i-th component  (helper)
proof fn lemma_dot_e0<T: Ring>(v: Vec3<T>)
    ensures
        dot(Vec3::<T> { x: T::one(), y: T::zero(), z: T::zero() }, v).eqv(v.x),
{
    // dot(e0, v) = (1*v.x + 0*v.y) + 0*v.z
    ring_lemmas::lemma_mul_one_left::<T>(v.x);
    ring_lemmas::lemma_mul_zero_left::<T>(v.y);
    ring_lemmas::lemma_mul_zero_left::<T>(v.z);

    // 1*v.x + 0*v.y ≡ v.x + 0 ≡ v.x
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().mul(v.x), v.x, T::zero().mul(v.y), T::zero(),
    );
    T::axiom_add_zero_right(v.x);
    T::axiom_eqv_transitive(
        T::one().mul(v.x).add(T::zero().mul(v.y)),
        v.x.add(T::zero()), v.x,
    );

    // (1*v.x + 0*v.y) + 0*v.z ≡ v.x + 0 ≡ v.x
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().mul(v.x).add(T::zero().mul(v.y)), v.x,
        T::zero().mul(v.z), T::zero(),
    );
    T::axiom_add_zero_right(v.x);
    T::axiom_eqv_transitive(
        dot(Vec3::<T> { x: T::one(), y: T::zero(), z: T::zero() }, v),
        v.x.add(T::zero()), v.x,
    );
}

proof fn lemma_dot_e1<T: Ring>(v: Vec3<T>)
    ensures
        dot(Vec3::<T> { x: T::zero(), y: T::one(), z: T::zero() }, v).eqv(v.y),
{
    ring_lemmas::lemma_mul_zero_left::<T>(v.x);
    ring_lemmas::lemma_mul_one_left::<T>(v.y);
    ring_lemmas::lemma_mul_zero_left::<T>(v.z);

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
        dot(Vec3::<T> { x: T::zero(), y: T::one(), z: T::zero() }, v),
        v.y.add(T::zero()), v.y,
    );
}

proof fn lemma_dot_e2<T: Ring>(v: Vec3<T>)
    ensures
        dot(Vec3::<T> { x: T::zero(), y: T::zero(), z: T::one() }, v).eqv(v.z),
{
    ring_lemmas::lemma_mul_zero_left::<T>(v.x);
    ring_lemmas::lemma_mul_zero_left::<T>(v.y);
    ring_lemmas::lemma_mul_one_left::<T>(v.z);

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
        dot(Vec3::<T> { x: T::zero(), y: T::zero(), z: T::one() }, v),
        T::zero().add(v.z), v.z,
    );
}

proof fn lemma_dot_e0_right<T: Ring>(v: Vec3<T>)
    ensures
        dot(v, Vec3::<T> { x: T::one(), y: T::zero(), z: T::zero() }).eqv(v.x),
{
    let e0 = Vec3::<T> { x: T::one(), y: T::zero(), z: T::zero() };
    crate::vec3::ops::lemma_dot_commutative(v, e0);
    lemma_dot_e0(v);
    T::axiom_eqv_transitive(dot(v, e0), dot(e0, v), v.x);
}

proof fn lemma_dot_e1_right<T: Ring>(v: Vec3<T>)
    ensures
        dot(v, Vec3::<T> { x: T::zero(), y: T::one(), z: T::zero() }).eqv(v.y),
{
    let e1 = Vec3::<T> { x: T::zero(), y: T::one(), z: T::zero() };
    crate::vec3::ops::lemma_dot_commutative(v, e1);
    lemma_dot_e1(v);
    T::axiom_eqv_transitive(dot(v, e1), dot(e1, v), v.y);
}

proof fn lemma_dot_e2_right<T: Ring>(v: Vec3<T>)
    ensures
        dot(v, Vec3::<T> { x: T::zero(), y: T::zero(), z: T::one() }).eqv(v.z),
{
    let e2 = Vec3::<T> { x: T::zero(), y: T::zero(), z: T::one() };
    crate::vec3::ops::lemma_dot_commutative(v, e2);
    lemma_dot_e2(v);
    T::axiom_eqv_transitive(dot(v, e2), dot(e2, v), v.z);
}

/// mat_vec_mul(identity(), v) ≡ v
pub proof fn lemma_identity_mul_vec<T: Ring>(v: Vec3<T>)
    ensures
        mat_vec_mul(identity(), v).eqv(v),
{
    lemma_dot_e0(v);
    lemma_dot_e1(v);
    lemma_dot_e2(v);
}

// ---------------------------------------------------------------------------
// Determinant lemmas (delegate to triple product)
// ---------------------------------------------------------------------------

/// det(swap rows 0,1) ≡ -det(m)
pub proof fn lemma_det_swap_rows_01<T: Ring>(m: Mat3x3<T>)
    ensures
        det(Mat3x3 { row0: m.row1, row1: m.row0, row2: m.row2 }).eqv(det(m).neg()),
{
    crate::vec3::ops::lemma_triple_swap_12(m.row0, m.row1, m.row2);
    T::axiom_eqv_symmetric(
        triple(m.row0, m.row1, m.row2),
        triple(m.row1, m.row0, m.row2).neg(),
    );
    additive_group_lemmas::lemma_neg_involution::<T>(triple(m.row1, m.row0, m.row2));
    // triple(m.row0, m.row1, m.row2) ≡ -(triple(m.row1, m.row0, m.row2))
    // reversed: -(triple(m.row1, m.row0, m.row2)) ≡ triple(m.row0, m.row1, m.row2)
    // What we actually need: triple(m.row1, m.row0, m.row2) ≡ -(triple(m.row0, m.row1, m.row2))
    // From swap_12: triple(m.row0, m.row1, m.row2) ≡ -(triple(m.row1, m.row0, m.row2))
    // So: triple(m.row1, m.row0, m.row2) ≡ -(triple(m.row0, m.row1, m.row2))
    // This follows from: if a ≡ -b, then b ≡ -a (negate both sides, use involution)
    // triple(m.row0, ...) ≡ -(triple(m.row1, ...))
    // neg both: -(triple(m.row0, ...)) ≡ -(-(triple(m.row1, ...))) ≡ triple(m.row1, ...)
    // symmetric: triple(m.row1, ...) ≡ -(triple(m.row0, ...))
    additive_group_lemmas::lemma_neg_congruence::<T>(
        triple(m.row0, m.row1, m.row2),
        triple(m.row1, m.row0, m.row2).neg(),
    );
    T::axiom_eqv_transitive(
        triple(m.row0, m.row1, m.row2).neg(),
        triple(m.row1, m.row0, m.row2).neg().neg(),
        triple(m.row1, m.row0, m.row2),
    );
    T::axiom_eqv_symmetric(
        triple(m.row0, m.row1, m.row2).neg(),
        triple(m.row1, m.row0, m.row2),
    );
}

/// det(swap rows 1,2) ≡ -det(m)
pub proof fn lemma_det_swap_rows_12<T: Ring>(m: Mat3x3<T>)
    ensures
        det(Mat3x3 { row0: m.row0, row1: m.row2, row2: m.row1 }).eqv(det(m).neg()),
{
    crate::vec3::ops::lemma_triple_swap_23(m.row0, m.row1, m.row2);
    // triple(m.row0, m.row2, m.row1) ≡ -(triple(m.row0, m.row1, m.row2))
    // swap_23 gives: triple(a, c, b) ≡ -(triple(a, b, c))
    // So: triple(m.row0, m.row2, m.row1) ≡ -(triple(m.row0, m.row1, m.row2)) = -det(m)
}

/// det(cyclic permutation of rows) ≡ det(m)
pub proof fn lemma_det_cyclic<T: Ring>(m: Mat3x3<T>)
    ensures
        det(Mat3x3 { row0: m.row1, row1: m.row2, row2: m.row0 }).eqv(det(m)),
{
    crate::vec3::ops::lemma_triple_cyclic(m.row0, m.row1, m.row2);
    T::axiom_eqv_symmetric(
        triple(m.row0, m.row1, m.row2),
        triple(m.row1, m.row2, m.row0),
    );
}

/// det(m) ≡ 0 when two rows are the same (rows 0,1)
pub proof fn lemma_det_zero_repeated_row_01<T: Ring>(a: Vec3<T>, b: Vec3<T>)
    ensures
        det(Mat3x3 { row0: a, row1: a, row2: b }).eqv(T::zero()),
{
    crate::vec3::ops::lemma_triple_self_zero_12(a, b);
}

/// det(m) ≡ 0 when two rows are the same (rows 1,2)
pub proof fn lemma_det_zero_repeated_row_12<T: Ring>(a: Vec3<T>, b: Vec3<T>)
    ensures
        det(Mat3x3 { row0: a, row1: b, row2: b }).eqv(T::zero()),
{
    crate::vec3::ops::lemma_triple_self_zero_23(a, b);
}

/// det is linear in the first row
pub proof fn lemma_det_linear_first_row<T: Ring>(r0: Vec3<T>, r0b: Vec3<T>, r1: Vec3<T>, r2: Vec3<T>)
    ensures
        det(Mat3x3 { row0: r0.add(r0b), row1: r1, row2: r2 }).eqv(
            det(Mat3x3 { row0: r0, row1: r1, row2: r2 }).add(
                det(Mat3x3 { row0: r0b, row1: r1, row2: r2 })
            )
        ),
{
    crate::vec3::ops::lemma_triple_linear_first(r0, r0b, r1, r2);
}

// ---------------------------------------------------------------------------
// Identity matrix multiplication
// ---------------------------------------------------------------------------

/// mat_mul(identity(), m).row_i ≡ m.row_i
pub proof fn lemma_identity_mat_mul_left<T: Ring>(m: Mat3x3<T>)
    ensures
        mat_mul(identity(), m).row0.eqv(m.row0),
        mat_mul(identity(), m).row1.eqv(m.row1),
        mat_mul(identity(), m).row2.eqv(m.row2),
{
    let bt = transpose(m);
    // Row 0: dot(e0, bt.row_j) ≡ bt.row_j.x = m.row0.{x,y,z}
    lemma_dot_e0(bt.row0);
    lemma_dot_e0(bt.row1);
    lemma_dot_e0(bt.row2);
    // Row 1: dot(e1, bt.row_j) ≡ bt.row_j.y = m.row1.{x,y,z}
    lemma_dot_e1(bt.row0);
    lemma_dot_e1(bt.row1);
    lemma_dot_e1(bt.row2);
    // Row 2: dot(e2, bt.row_j) ≡ bt.row_j.z = m.row2.{x,y,z}
    lemma_dot_e2(bt.row0);
    lemma_dot_e2(bt.row1);
    lemma_dot_e2(bt.row2);
}

/// mat_mul(m, identity()).row_i ≡ m.row_i
pub proof fn lemma_identity_mat_mul_right<T: Ring>(m: Mat3x3<T>)
    ensures
        mat_mul(m, identity()).row0.eqv(m.row0),
        mat_mul(m, identity()).row1.eqv(m.row1),
        mat_mul(m, identity()).row2.eqv(m.row2),
{
    // transpose(identity()) = identity(), so columns of I are e0, e1, e2
    // dot(m.row_i, e_j) ≡ m.row_i.component_j
    lemma_dot_e0_right(m.row0);
    lemma_dot_e1_right(m.row0);
    lemma_dot_e2_right(m.row0);
    lemma_dot_e0_right(m.row1);
    lemma_dot_e1_right(m.row1);
    lemma_dot_e2_right(m.row1);
    lemma_dot_e0_right(m.row2);
    lemma_dot_e1_right(m.row2);
    lemma_dot_e2_right(m.row2);
}

// ---------------------------------------------------------------------------
// Determinant: identity and congruence
// ---------------------------------------------------------------------------

/// a - 0 ≡ a (private helper)
proof fn lemma_sub_zero_right<T: Ring>(a: T)
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
    // det(I) = triple(e0, e1, e2) = dot(e0, cross(e1, e2))
    let e0 = Vec3::<T> { x: T::one(),  y: T::zero(), z: T::zero() };
    let e1 = Vec3::<T> { x: T::zero(), y: T::one(),  z: T::zero() };
    let e2 = Vec3::<T> { x: T::zero(), y: T::zero(), z: T::one()  };

    // cross(e1, e2):
    //   x = 1*1 - 0*0, y = 0*0 - 0*1, z = 0*0 - 1*0
    // Show cross(e1, e2) ≡ e0

    // x component: 1*1 - 0*0 ≡ 1 - 0 ≡ 1
    T::axiom_mul_one_right(T::one());
    ring_lemmas::lemma_mul_zero_left::<T>(T::zero());
    additive_group_lemmas::lemma_sub_congruence::<T>(
        T::one().mul(T::one()), T::one(),
        T::zero().mul(T::zero()), T::zero(),
    );
    lemma_sub_zero_right::<T>(T::one());
    T::axiom_eqv_transitive(
        cross(e1, e2).x,
        T::one().sub(T::zero()),
        T::one(),
    );

    // y component: 0*0 - 0*1 ≡ 0 - 0 ≡ 0
    ring_lemmas::lemma_mul_zero_left::<T>(T::zero());
    ring_lemmas::lemma_mul_zero_left::<T>(T::one());
    additive_group_lemmas::lemma_sub_congruence::<T>(
        T::zero().mul(T::zero()), T::zero(),
        T::zero().mul(T::one()), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(
        cross(e1, e2).y,
        T::zero().sub(T::zero()),
        T::zero(),
    );

    // z component: 0*0 - 1*0 ≡ 0 - 0 ≡ 0
    ring_lemmas::lemma_mul_zero_left::<T>(T::zero());
    T::axiom_mul_zero_right(T::one());
    additive_group_lemmas::lemma_sub_congruence::<T>(
        T::zero().mul(T::zero()), T::zero(),
        T::one().mul(T::zero()), T::zero(),
    );
    additive_group_lemmas::lemma_sub_self::<T>(T::zero());
    T::axiom_eqv_transitive(
        cross(e1, e2).z,
        T::zero().sub(T::zero()),
        T::zero(),
    );

    // Now cross(e1, e2) ≡ e0
    // dot(e0, cross(e1, e2)) ≡ dot(e0, e0) via dot_congruence
    <Vec3<T> as Equivalence>::axiom_eqv_reflexive(e0);
    crate::vec3::ops::lemma_dot_congruence(e0, e0, cross(e1, e2), e0);

    // dot(e0, e0) ≡ e0.x = 1  (by lemma_dot_e0)
    lemma_dot_e0(e0);
    T::axiom_eqv_transitive(
        det(identity::<T>()),
        dot(e0, e0),
        T::one(),
    );
}

/// Determinant respects row-wise equivalence
pub proof fn lemma_det_congruence<T: Ring>(a: Mat3x3<T>, b: Mat3x3<T>)
    requires
        a.row0.eqv(b.row0),
        a.row1.eqv(b.row1),
        a.row2.eqv(b.row2),
    ensures
        det(a).eqv(det(b)),
{
    // det = triple(row0, row1, row2) = dot(row0, cross(row1, row2))
    // cross(a.row1, a.row2) ≡ cross(b.row1, b.row2) via cross_congruence
    crate::vec3::ops::lemma_cross_congruence(a.row1, b.row1, a.row2, b.row2);
    // dot(a.row0, cross(a.row1, a.row2)) ≡ dot(b.row0, cross(b.row1, b.row2)) via dot_congruence
    crate::vec3::ops::lemma_dot_congruence(
        a.row0, b.row0,
        cross(a.row1, a.row2), cross(b.row1, b.row2),
    );
}

// ---------------------------------------------------------------------------
// Adjugate and inverse definitions
// ---------------------------------------------------------------------------

pub open spec fn adjugate<T: Ring>(m: Mat3x3<T>) -> Mat3x3<T> {
    let c12 = cross(m.row1, m.row2);
    let c20 = cross(m.row2, m.row0);
    let c01 = cross(m.row0, m.row1);
    // Transpose of [c12, c20, c01] — columns are the cross products
    Mat3x3 {
        row0: Vec3 { x: c12.x, y: c20.x, z: c01.x },
        row1: Vec3 { x: c12.y, y: c20.y, z: c01.y },
        row2: Vec3 { x: c12.z, y: c20.z, z: c01.z },
    }
}

pub open spec fn inverse<T: Field>(m: Mat3x3<T>) -> Mat3x3<T> {
    let d_inv = det(m).recip();
    let adj = adjugate(m);
    Mat3x3 {
        row0: scale(d_inv, adj.row0),
        row1: scale(d_inv, adj.row1),
        row2: scale(d_inv, adj.row2),
    }
}

// ---------------------------------------------------------------------------
// m * adj(m) ≡ det(m) * I
// ---------------------------------------------------------------------------

/// m * adjugate(m) has det(m) on diagonal, 0 off-diagonal
proof fn lemma_mat_mul_adjugate_right<T: Ring>(m: Mat3x3<T>)
    ensures
        mat_mul(m, adjugate(m)).row0.eqv(Vec3 { x: det(m), y: T::zero(), z: T::zero() }),
        mat_mul(m, adjugate(m)).row1.eqv(Vec3 { x: T::zero(), y: det(m), z: T::zero() }),
        mat_mul(m, adjugate(m)).row2.eqv(Vec3 { x: T::zero(), y: T::zero(), z: det(m) }),
{
    let r0 = m.row0;
    let r1 = m.row1;
    let r2 = m.row2;
    let adj = adjugate(m);
    let t_adj = transpose(adj);

    // Key: transpose(adj).row0 = cross(r1,r2), row1 = cross(r2,r0), row2 = cross(r0,r1)
    // These are structurally (definitionally) equal, so no proof needed.

    // mat_mul(m, adj).row_i.j = dot(m.row_i, t_adj.row_j) = triple(row_i, ?, ?)

    // --- Diagonal entries: ≡ det(m) ---

    // (0,0): dot(r0, cross(r1,r2)) = triple(r0,r1,r2) = det(m)  [definitional]
    T::axiom_eqv_reflexive(det(m));

    // (1,1): dot(r1, cross(r2,r0)) = triple(r1,r2,r0) ≡ triple(r0,r1,r2) = det(m)
    crate::vec3::ops::lemma_triple_cyclic(r0, r1, r2);
    // triple_cyclic gives: triple(r0,r1,r2) ≡ triple(r1,r2,r0)
    T::axiom_eqv_symmetric(triple(r0, r1, r2), triple(r1, r2, r0));
    // triple(r1,r2,r0) ≡ det(m)

    // (2,2): dot(r2, cross(r0,r1)) = triple(r2,r0,r1) ≡ det(m)
    // triple(r0,r1,r2) ≡ triple(r1,r2,r0) ≡ triple(r2,r0,r1) via double cyclic
    crate::vec3::ops::lemma_triple_cyclic(r1, r2, r0);
    // triple(r1,r2,r0) ≡ triple(r2,r0,r1)
    T::axiom_eqv_transitive(triple(r0, r1, r2), triple(r1, r2, r0), triple(r2, r0, r1));
    T::axiom_eqv_symmetric(triple(r0, r1, r2), triple(r2, r0, r1));
    // triple(r2,r0,r1) ≡ det(m)

    // --- Off-diagonal entries: ≡ 0 ---

    // (0,1): dot(r0, cross(r2,r0)) = triple(r0,r2,r0) ≡ 0
    crate::vec3::ops::lemma_triple_self_zero_13(r0, r2);

    // (0,2): dot(r0, cross(r0,r1)) = triple(r0,r0,r1) ≡ 0
    crate::vec3::ops::lemma_triple_self_zero_12(r0, r1);

    // (1,0): dot(r1, cross(r1,r2)) = triple(r1,r1,r2) ≡ 0
    crate::vec3::ops::lemma_triple_self_zero_12(r1, r2);

    // (1,2): dot(r1, cross(r0,r1)) = triple(r1,r0,r1) ≡ 0
    crate::vec3::ops::lemma_triple_self_zero_13(r1, r0);

    // (2,0): dot(r2, cross(r1,r2)) = triple(r2,r1,r2) ≡ 0
    crate::vec3::ops::lemma_triple_self_zero_13(r2, r1);

    // (2,1): dot(r2, cross(r2,r0)) = triple(r2,r2,r0) ≡ 0
    crate::vec3::ops::lemma_triple_self_zero_12(r2, r0);
}

// ---------------------------------------------------------------------------
// 3-factor product helpers
// ---------------------------------------------------------------------------

/// (a*b)*c ≡ c*(a*b) [commutativity of outer product]
proof fn lemma_mul3_outer_comm<T: Ring>(a: T, b: T, c: T)
    ensures
        a.mul(b).mul(c).eqv(c.mul(a.mul(b))),
{
    T::axiom_mul_commutative(a.mul(b), c);
}

/// (a*b)*c ≡ (c*a)*b [rotate right: move c to front]
proof fn lemma_mul3_rotate_right<T: Ring>(a: T, b: T, c: T)
    ensures
        a.mul(b).mul(c).eqv(c.mul(a).mul(b)),
{
    lemma_mul3_outer_comm::<T>(a, b, c);
    // (a*b)*c ≡ c*(a*b)
    T::axiom_mul_associative(c, a, b);
    // (c*a)*b ≡ c*(a*b) → flip to c*(a*b) ≡ (c*a)*b
    T::axiom_eqv_symmetric(c.mul(a).mul(b), c.mul(a.mul(b)));
    T::axiom_eqv_transitive(
        a.mul(b).mul(c),
        c.mul(a.mul(b)),
        c.mul(a).mul(b),
    );
}

/// (a*b)*c ≡ (b*c)*a [rotate left: move a to end]
proof fn lemma_mul3_rotate_left<T: Ring>(a: T, b: T, c: T)
    ensures
        a.mul(b).mul(c).eqv(b.mul(c).mul(a)),
{
    T::axiom_mul_associative(a, b, c);
    T::axiom_mul_commutative(a, b.mul(c));
    T::axiom_eqv_transitive(
        a.mul(b).mul(c),
        a.mul(b.mul(c)),
        b.mul(c).mul(a),
    );
}

// ---------------------------------------------------------------------------
// Additional three-factor product helpers
// ---------------------------------------------------------------------------

/// a*(b*c) ≡ b*(a*c) [swap first two factors in a*(b*c) form]
proof fn lemma_mul3_swap12<T: Ring>(a: T, b: T, c: T)
    ensures
        a.mul(b.mul(c)).eqv(b.mul(a.mul(c))),
{
    // (a*b)*c ≡ a*(b*c)    [associativity]  →  flip to a*(b*c) ≡ (a*b)*c
    // (a*b)*c ≡ (b*a)*c    [inner commutativity + congruence]
    // (b*a)*c ≡ b*(a*c)    [associativity]  →  flip
    T::axiom_mul_associative(a, b, c);
    T::axiom_eqv_symmetric(a.mul(b).mul(c), a.mul(b.mul(c)));
    // now: a*(b*c) ≡ (a*b)*c
    T::axiom_mul_commutative(a, b);
    T::axiom_eqv_reflexive(c);
    ring_lemmas::lemma_mul_congruence::<T>(a.mul(b), b.mul(a), c, c);
    // now: (a*b)*c ≡ (b*a)*c
    T::axiom_eqv_transitive(a.mul(b.mul(c)), a.mul(b).mul(c), b.mul(a).mul(c));
    // now: a*(b*c) ≡ (b*a)*c
    T::axiom_mul_associative(b, a, c);
    // now: (b*a)*c ≡ b*(a*c)
    T::axiom_eqv_transitive(a.mul(b.mul(c)), b.mul(a).mul(c), b.mul(a.mul(c)));
}

/// (a-b) + (c-d) ≡ (c-b) + (a-d)  [swap first operands of two subs in a sum]
proof fn lemma_sub_add_swap<T: Ring>(a: T, b: T, c: T, d: T)
    ensures
        a.sub(b).add(c.sub(d)).eqv(c.sub(b).add(a.sub(d))),
{
    // Convert subs to add_neg
    T::axiom_sub_is_add_neg(a, b);
    T::axiom_sub_is_add_neg(c, d);
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.sub(b), a.add(b.neg()), c.sub(d), c.add(d.neg()),
    );
    // (a-b)+(c-d) ≡ (a+(-b))+(c+(-d))

    // Rearrange: (a+(-b))+(c+(-d)) ≡ (a+c)+((-b)+(-d))
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a, b.neg(), c, d.neg());
    T::axiom_eqv_transitive(
        a.sub(b).add(c.sub(d)),
        a.add(b.neg()).add(c.add(d.neg())),
        a.add(c).add(b.neg().add(d.neg())),
    );

    // Same for RHS: (c-b)+(a-d) ≡ (c+a)+((-b)+(-d))
    T::axiom_sub_is_add_neg(c, b);
    T::axiom_sub_is_add_neg(a, d);
    additive_group_lemmas::lemma_add_congruence::<T>(
        c.sub(b), c.add(b.neg()), a.sub(d), a.add(d.neg()),
    );
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(c, b.neg(), a, d.neg());
    T::axiom_eqv_transitive(
        c.sub(b).add(a.sub(d)),
        c.add(b.neg()).add(a.add(d.neg())),
        c.add(a).add(b.neg().add(d.neg())),
    );

    // Show a+c ≡ c+a
    T::axiom_add_commutative(a, c);
    T::axiom_eqv_reflexive(b.neg().add(d.neg()));
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(c), c.add(a), b.neg().add(d.neg()), b.neg().add(d.neg()),
    );
    // (a+c)+((-b)+(-d)) ≡ (c+a)+((-b)+(-d))

    // Chain: LHS ≡ (a+c)+(neg_sum) ≡ (c+a)+(neg_sum)
    T::axiom_eqv_transitive(
        a.sub(b).add(c.sub(d)),
        a.add(c).add(b.neg().add(d.neg())),
        c.add(a).add(b.neg().add(d.neg())),
    );

    // RHS ≡ (c+a)+(neg_sum), so use symmetry + transitivity
    T::axiom_eqv_symmetric(
        c.sub(b).add(a.sub(d)),
        c.add(a).add(b.neg().add(d.neg())),
    );
    T::axiom_eqv_transitive(
        a.sub(b).add(c.sub(d)),
        c.add(a).add(b.neg().add(d.neg())),
        c.sub(b).add(a.sub(d)),
    );
}

// ---------------------------------------------------------------------------
// Adjugate–transpose relationship
// ---------------------------------------------------------------------------

/// adjugate(m).row_i ≡ transpose(adjugate(m^T)).row_i
///
/// Each component of adj(m) differs from the corresponding component of
/// transpose(adj(m^T)) only by commutativity in the subtrahend of a cross
/// product component.
proof fn lemma_adjugate_transpose_rows<T: Ring>(m: Mat3x3<T>)
    ensures
        adjugate(m).row0.eqv(transpose(adjugate(transpose(m))).row0),
        adjugate(m).row1.eqv(transpose(adjugate(transpose(m))).row1),
        adjugate(m).row2.eqv(transpose(adjugate(transpose(m))).row2),
{
    let r0 = m.row0;
    let r1 = m.row1;
    let r2 = m.row2;

    // adj(m).row0 = (cross(r1,r2).x, cross(r2,r0).x, cross(r0,r1).x)
    // transpose(adj(m^T)).row0 = cross(col1, col2)
    //   where col1 = (r0.y, r1.y, r2.y), col2 = (r0.z, r1.z, r2.z)
    //
    // Each component pair: a*b - c*d vs a*b - d*c  [only subtrahend differs by commutativity]

    // Row 0, component x: cross(r1,r2).x = r1.y*r2.z - r1.z*r2.y
    //                      cross(col1,col2).x = r1.y*r2.z - r2.y*r1.z
    T::axiom_eqv_reflexive(r1.y.mul(r2.z));
    T::axiom_mul_commutative(r1.z, r2.y);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        r1.y.mul(r2.z), r1.y.mul(r2.z), r1.z.mul(r2.y), r2.y.mul(r1.z),
    );

    // Row 0, component y: cross(r2,r0).x = r2.y*r0.z - r2.z*r0.y
    //                      cross(col1,col2).y = r2.y*r0.z - r0.y*r2.z
    T::axiom_eqv_reflexive(r2.y.mul(r0.z));
    T::axiom_mul_commutative(r2.z, r0.y);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        r2.y.mul(r0.z), r2.y.mul(r0.z), r2.z.mul(r0.y), r0.y.mul(r2.z),
    );

    // Row 0, component z: cross(r0,r1).x = r0.y*r1.z - r0.z*r1.y
    //                      cross(col1,col2).z = r0.y*r1.z - r1.y*r0.z
    T::axiom_eqv_reflexive(r0.y.mul(r1.z));
    T::axiom_mul_commutative(r0.z, r1.y);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        r0.y.mul(r1.z), r0.y.mul(r1.z), r0.z.mul(r1.y), r1.y.mul(r0.z),
    );

    // Row 1, component x: cross(r1,r2).y = r1.z*r2.x - r1.x*r2.z
    //                      cross(col2,col0).x = r1.z*r2.x - r2.z*r1.x
    T::axiom_eqv_reflexive(r1.z.mul(r2.x));
    T::axiom_mul_commutative(r1.x, r2.z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        r1.z.mul(r2.x), r1.z.mul(r2.x), r1.x.mul(r2.z), r2.z.mul(r1.x),
    );

    // Row 1, component y: cross(r2,r0).y = r2.z*r0.x - r2.x*r0.z
    //                      cross(col2,col0).y = r2.z*r0.x - r0.z*r2.x
    T::axiom_eqv_reflexive(r2.z.mul(r0.x));
    T::axiom_mul_commutative(r2.x, r0.z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        r2.z.mul(r0.x), r2.z.mul(r0.x), r2.x.mul(r0.z), r0.z.mul(r2.x),
    );

    // Row 1, component z: cross(r0,r1).y = r0.z*r1.x - r0.x*r1.z
    //                      cross(col2,col0).z = r0.z*r1.x - r1.z*r0.x
    T::axiom_eqv_reflexive(r0.z.mul(r1.x));
    T::axiom_mul_commutative(r0.x, r1.z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        r0.z.mul(r1.x), r0.z.mul(r1.x), r0.x.mul(r1.z), r1.z.mul(r0.x),
    );

    // Row 2, component x: cross(r1,r2).z = r1.x*r2.y - r1.y*r2.x
    //                      cross(col0,col1).x = r1.x*r2.y - r2.x*r1.y
    T::axiom_eqv_reflexive(r1.x.mul(r2.y));
    T::axiom_mul_commutative(r1.y, r2.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        r1.x.mul(r2.y), r1.x.mul(r2.y), r1.y.mul(r2.x), r2.x.mul(r1.y),
    );

    // Row 2, component y: cross(r2,r0).z = r2.x*r0.y - r2.y*r0.x
    //                      cross(col0,col1).y = r2.x*r0.y - r0.x*r2.y
    T::axiom_eqv_reflexive(r2.x.mul(r0.y));
    T::axiom_mul_commutative(r2.y, r0.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        r2.x.mul(r0.y), r2.x.mul(r0.y), r2.y.mul(r0.x), r0.x.mul(r2.y),
    );

    // Row 2, component z: cross(r0,r1).z = r0.x*r1.y - r0.y*r1.x
    //                      cross(col0,col1).z = r0.x*r1.y - r1.x*r0.y
    T::axiom_eqv_reflexive(r0.x.mul(r1.y));
    T::axiom_mul_commutative(r0.y, r1.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        r0.x.mul(r1.y), r0.x.mul(r1.y), r0.y.mul(r1.x), r1.x.mul(r0.y),
    );
}

// ---------------------------------------------------------------------------
// Determinant transpose
// ---------------------------------------------------------------------------

/// det(m^T) ≡ det(m)
pub proof fn lemma_det_transpose<T: Ring>(m: Mat3x3<T>)
    ensures
        det(transpose(m)).eqv(det(m)),
{
    let r0 = m.row0;
    let r1 = m.row1;
    let r2 = m.row2;
    let mt = transpose(m);
    let adj = adjugate(m);

    // --- Part 1: det(m^T) ≡ dot(col0, adj.row0) ---
    // adj.row0 ≡ cross(col1, col2) [adjugate_transpose flipped]
    lemma_adjugate_transpose_rows::<T>(m);
    Vec3::<T>::axiom_eqv_symmetric(adj.row0, transpose(adjugate(mt)).row0);
    // transpose(adjugate(mt)).row0 = cross(mt.row1, mt.row2) definitionally
    Vec3::<T>::axiom_eqv_reflexive(mt.row0);
    crate::vec3::ops::lemma_dot_congruence(
        mt.row0, mt.row0, cross(mt.row1, mt.row2), adj.row0,
    );
    // det(mt) = dot(mt.row0, cross(mt.row1,mt.row2)) ≡ dot(mt.row0, adj.row0)

    // --- Part 2: dot(mt.row0, adj.row0) ≡ det(m) ---
    //
    // dot(mt.row0, adj.row0) = P + Q1 + Q2  (left-assoc)
    //   where P  = r0.x * cross(r1,r2).x
    //         Q1 = r1.x * cross(r2,r0).x
    //         Q2 = r2.x * cross(r0,r1).x
    //
    // det(m) = dot(r0, cross(r1,r2)) = P + R1 + R2  (left-assoc)
    //   where R1 = r0.y * cross(r1,r2).y
    //         R2 = r0.z * cross(r1,r2).z
    //
    // Strategy: assoc out P, show Q1+Q2 ≡ R1+R2 via sub_add_swap, assoc back.

    let c12 = cross(r1, r2);
    let p  = r0.x.mul(c12.x);
    let q1 = r1.x.mul(cross(r2, r0).x);
    let q2 = r2.x.mul(cross(r0, r1).x);
    let r1v = r0.y.mul(c12.y);
    let r2v = r0.z.mul(c12.z);

    // Step 2a: associativity  (P+Q1)+Q2 ≡ P+(Q1+Q2)
    T::axiom_add_associative(p, q1, q2);

    // Step 2b: distribute Q1 and Q2
    // Q1 = r1.x * (r2.y*r0.z - r2.z*r0.y) ≡ A - B
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(r1.x, r2.y.mul(r0.z), r2.z.mul(r0.y));
    // Q2 = r2.x * (r0.y*r1.z - r0.z*r1.y) ≡ C - D
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(r2.x, r0.y.mul(r1.z), r0.z.mul(r1.y));

    let a = r1.x.mul(r2.y.mul(r0.z));
    let b = r1.x.mul(r2.z.mul(r0.y));
    let c = r2.x.mul(r0.y.mul(r1.z));
    let d = r2.x.mul(r0.z.mul(r1.y));

    // Q1+Q2 ≡ (A-B)+(C-D)
    additive_group_lemmas::lemma_add_congruence::<T>(q1, a.sub(b), q2, c.sub(d));

    // Step 2c: sub_add_swap  (A-B)+(C-D) ≡ (C-B)+(A-D)
    lemma_sub_add_swap::<T>(a, b, c, d);

    // Step 2d: rearrange each factor triple
    // A = r1.x*(r2.y*r0.z) ≡ r0.z*(r1.x*r2.y) = A'
    T::axiom_mul_associative(r1.x, r2.y, r0.z);
    T::axiom_eqv_symmetric(r1.x.mul(r2.y).mul(r0.z), a);
    lemma_mul3_outer_comm::<T>(r1.x, r2.y, r0.z);
    T::axiom_eqv_transitive(a, r1.x.mul(r2.y).mul(r0.z), r0.z.mul(r1.x.mul(r2.y)));

    // B = r1.x*(r2.z*r0.y) ≡ r0.y*(r1.x*r2.z) = B'
    T::axiom_mul_associative(r1.x, r2.z, r0.y);
    T::axiom_eqv_symmetric(r1.x.mul(r2.z).mul(r0.y), b);
    lemma_mul3_outer_comm::<T>(r1.x, r2.z, r0.y);
    T::axiom_eqv_transitive(b, r1.x.mul(r2.z).mul(r0.y), r0.y.mul(r1.x.mul(r2.z)));

    // C = r2.x*(r0.y*r1.z) ≡ r0.y*(r1.z*r2.x) = C'
    lemma_mul3_swap12::<T>(r2.x, r0.y, r1.z);
    T::axiom_mul_commutative(r2.x, r1.z);
    ring_lemmas::lemma_mul_congruence_right::<T>(r0.y, r2.x.mul(r1.z), r1.z.mul(r2.x));
    T::axiom_eqv_transitive(c, r0.y.mul(r2.x.mul(r1.z)), r0.y.mul(r1.z.mul(r2.x)));

    // D = r2.x*(r0.z*r1.y) ≡ r0.z*(r1.y*r2.x) = D'
    lemma_mul3_swap12::<T>(r2.x, r0.z, r1.y);
    T::axiom_mul_commutative(r2.x, r1.y);
    ring_lemmas::lemma_mul_congruence_right::<T>(r0.z, r2.x.mul(r1.y), r1.y.mul(r2.x));
    T::axiom_eqv_transitive(d, r0.z.mul(r2.x.mul(r1.y)), r0.z.mul(r1.y.mul(r2.x)));

    let ap = r0.z.mul(r1.x.mul(r2.y));
    let bp = r0.y.mul(r1.x.mul(r2.z));
    let cp = r0.y.mul(r1.z.mul(r2.x));
    let dp = r0.z.mul(r1.y.mul(r2.x));

    // Step 2e: (C-B)+(A-D) ≡ (C'-B')+(A'-D')
    additive_group_lemmas::lemma_sub_congruence::<T>(c, cp, b, bp);
    additive_group_lemmas::lemma_sub_congruence::<T>(a, ap, d, dp);
    additive_group_lemmas::lemma_add_congruence::<T>(c.sub(b), cp.sub(bp), a.sub(d), ap.sub(dp));

    // Step 2f: reverse-distribute to recover R1 and R2
    // R1 = r0.y * (r1.z*r2.x - r1.x*r2.z) ≡ C' - B'
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(r0.y, r1.z.mul(r2.x), r1.x.mul(r2.z));
    T::axiom_eqv_symmetric(r1v, cp.sub(bp));
    // R2 = r0.z * (r1.x*r2.y - r1.y*r2.x) ≡ A' - D'
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(r0.z, r1.x.mul(r2.y), r1.y.mul(r2.x));
    T::axiom_eqv_symmetric(r2v, ap.sub(dp));

    // (C'-B')+(A'-D') ≡ R1+R2
    additive_group_lemmas::lemma_add_congruence::<T>(cp.sub(bp), r1v, ap.sub(dp), r2v);

    // Step 2g: chain Q1+Q2 ≡ R1+R2
    let lhs_d = a.sub(b).add(c.sub(d));
    let swapped = c.sub(b).add(a.sub(d));
    let primed = cp.sub(bp).add(ap.sub(dp));
    T::axiom_eqv_transitive(q1.add(q2), lhs_d, swapped);
    T::axiom_eqv_transitive(q1.add(q2), swapped, primed);
    T::axiom_eqv_transitive(q1.add(q2), primed, r1v.add(r2v));

    // Step 2h: P + (Q1+Q2) ≡ P + (R1+R2)
    T::axiom_eqv_reflexive(p);
    additive_group_lemmas::lemma_add_congruence::<T>(p, p, q1.add(q2), r1v.add(r2v));

    // Step 2i: reverse assoc  P+(R1+R2) ≡ (P+R1)+R2
    T::axiom_add_associative(p, r1v, r2v);
    T::axiom_eqv_symmetric(p.add(r1v).add(r2v), p.add(r1v.add(r2v)));

    // Step 2j: dot(mt.row0, adj.row0) = (P+Q1)+Q2 ≡ P+(Q1+Q2) ≡ P+(R1+R2) ≡ (P+R1)+R2 = det(m)
    T::axiom_eqv_transitive(
        dot(mt.row0, adj.row0), p.add(q1.add(q2)), p.add(r1v.add(r2v)),
    );
    T::axiom_eqv_transitive(
        dot(mt.row0, adj.row0), p.add(r1v.add(r2v)), det(m),
    );

    // --- Part 3: final chain  det(m^T) ≡ dot(col0, adj.row0) ≡ det(m) ---
    T::axiom_eqv_transitive(det(mt), dot(mt.row0, adj.row0), det(m));
}

// ---------------------------------------------------------------------------
// Left adjugate product
// ---------------------------------------------------------------------------

/// adjugate(m) * m has det(m) on diagonal, 0 off-diagonal
proof fn lemma_mat_mul_adjugate_left<T: Ring>(m: Mat3x3<T>)
    ensures
        mat_mul(adjugate(m), m).row0.eqv(Vec3 { x: det(m), y: T::zero(), z: T::zero() }),
        mat_mul(adjugate(m), m).row1.eqv(Vec3 { x: T::zero(), y: det(m), z: T::zero() }),
        mat_mul(adjugate(m), m).row2.eqv(Vec3 { x: T::zero(), y: T::zero(), z: det(m) }),
{
    let mt = transpose(m);
    let adj = adjugate(m);
    let adj_mt = adjugate(mt);

    // Right adjugate of m^T: m^T * adj(m^T) has det(m^T) on diagonal, 0 off-diagonal
    lemma_mat_mul_adjugate_right::<T>(mt);
    // adj(m).row_i ≡ transpose(adj(m^T)).row_i
    lemma_adjugate_transpose_rows::<T>(m);
    // det(m^T) ≡ det(m)
    lemma_det_transpose::<T>(m);

    // For each entry (i,j) of adj*m:
    //   (adj*m)_{i,j} = dot(adj.row_i, transpose(m).row_j) = dot(adj.row_i, mt.row_j)
    //   ≡ dot(mt.row_j, adj.row_i)                  [dot_commutative]
    //   ≡ dot(mt.row_j, t_adj_mt.row_i)             [dot_congruence via adjugate_transpose]
    //   = mat_mul(mt, adj_mt) entry (j,i)            [definitional]
    //
    // Diagonal (i=j): ≡ det(mt) ≡ det(m)
    // Off-diagonal (i≠j): ≡ 0

    // Helper: for each (i, cross_idx), chain the entry equivalence.
    // We need Vec3::axiom_eqv_reflexive for the mt.row_j argument of dot_congruence.
    Vec3::<T>::axiom_eqv_reflexive(mt.row0);
    Vec3::<T>::axiom_eqv_reflexive(mt.row1);
    Vec3::<T>::axiom_eqv_reflexive(mt.row2);

    // --- Row 0 of adj*m: entries (0,0), (0,1), (0,2) ---

    // dot_congruence for row_i=0: adj.row0 ≡ t_adj_mt.row0
    crate::vec3::ops::lemma_dot_congruence(mt.row0, mt.row0, adj.row0, transpose(adj_mt).row0);
    crate::vec3::ops::lemma_dot_congruence(mt.row1, mt.row1, adj.row0, transpose(adj_mt).row0);
    crate::vec3::ops::lemma_dot_congruence(mt.row2, mt.row2, adj.row0, transpose(adj_mt).row0);

    // (0,0): dot(adj.row0, mt.row0) ≡ dot(mt.row0, adj.row0) ≡ dot(mt.row0, t_adj_mt.row0)
    //        = mat_mul(mt, adj_mt).row0.x ≡ det(mt) ≡ det(m)
    crate::vec3::ops::lemma_dot_commutative(adj.row0, mt.row0);
    T::axiom_eqv_transitive(
        dot(adj.row0, mt.row0), dot(mt.row0, adj.row0), dot(mt.row0, transpose(adj_mt).row0),
    );
    // mat_mul(mt, adj_mt).row0.x = dot(mt.row0, transpose(adj_mt).row0) ≡ det(mt)
    // (from right adjugate of mt: row0.x.eqv(det(mt)))
    T::axiom_eqv_transitive(
        dot(adj.row0, mt.row0), dot(mt.row0, transpose(adj_mt).row0), det(mt),
    );
    T::axiom_eqv_transitive(dot(adj.row0, mt.row0), det(mt), det(m));

    // (0,1): dot(adj.row0, mt.row1) ≡ ... ≡ mat_mul(mt,adj_mt).row1.x ≡ 0
    crate::vec3::ops::lemma_dot_commutative(adj.row0, mt.row1);
    T::axiom_eqv_transitive(
        dot(adj.row0, mt.row1), dot(mt.row1, adj.row0), dot(mt.row1, transpose(adj_mt).row0),
    );
    T::axiom_eqv_transitive(
        dot(adj.row0, mt.row1), dot(mt.row1, transpose(adj_mt).row0), T::zero(),
    );

    // (0,2): dot(adj.row0, mt.row2) ≡ ... ≡ mat_mul(mt,adj_mt).row2.x ≡ 0
    crate::vec3::ops::lemma_dot_commutative(adj.row0, mt.row2);
    T::axiom_eqv_transitive(
        dot(adj.row0, mt.row2), dot(mt.row2, adj.row0), dot(mt.row2, transpose(adj_mt).row0),
    );
    T::axiom_eqv_transitive(
        dot(adj.row0, mt.row2), dot(mt.row2, transpose(adj_mt).row0), T::zero(),
    );

    // --- Row 1 of adj*m: entries (1,0), (1,1), (1,2) ---

    crate::vec3::ops::lemma_dot_congruence(mt.row0, mt.row0, adj.row1, transpose(adj_mt).row1);
    crate::vec3::ops::lemma_dot_congruence(mt.row1, mt.row1, adj.row1, transpose(adj_mt).row1);
    crate::vec3::ops::lemma_dot_congruence(mt.row2, mt.row2, adj.row1, transpose(adj_mt).row1);

    // (1,0): dot(adj.row1, mt.row0) ≡ ... ≡ mat_mul(mt,adj_mt).row0.y ≡ 0
    crate::vec3::ops::lemma_dot_commutative(adj.row1, mt.row0);
    T::axiom_eqv_transitive(
        dot(adj.row1, mt.row0), dot(mt.row0, adj.row1), dot(mt.row0, transpose(adj_mt).row1),
    );
    T::axiom_eqv_transitive(
        dot(adj.row1, mt.row0), dot(mt.row0, transpose(adj_mt).row1), T::zero(),
    );

    // (1,1): dot(adj.row1, mt.row1) ≡ dot(mt.row1, t_adj_mt.row1)
    //        = mat_mul(mt, adj_mt).row1.y ≡ det(mt) ≡ det(m)
    crate::vec3::ops::lemma_dot_commutative(adj.row1, mt.row1);
    T::axiom_eqv_transitive(
        dot(adj.row1, mt.row1), dot(mt.row1, adj.row1), dot(mt.row1, transpose(adj_mt).row1),
    );
    T::axiom_eqv_transitive(
        dot(adj.row1, mt.row1), dot(mt.row1, transpose(adj_mt).row1), det(mt),
    );
    T::axiom_eqv_transitive(dot(adj.row1, mt.row1), det(mt), det(m));

    // (1,2): dot(adj.row1, mt.row2) ≡ ... ≡ mat_mul(mt,adj_mt).row2.y ≡ 0
    crate::vec3::ops::lemma_dot_commutative(adj.row1, mt.row2);
    T::axiom_eqv_transitive(
        dot(adj.row1, mt.row2), dot(mt.row2, adj.row1), dot(mt.row2, transpose(adj_mt).row1),
    );
    T::axiom_eqv_transitive(
        dot(adj.row1, mt.row2), dot(mt.row2, transpose(adj_mt).row1), T::zero(),
    );

    // --- Row 2 of adj*m: entries (2,0), (2,1), (2,2) ---

    crate::vec3::ops::lemma_dot_congruence(mt.row0, mt.row0, adj.row2, transpose(adj_mt).row2);
    crate::vec3::ops::lemma_dot_congruence(mt.row1, mt.row1, adj.row2, transpose(adj_mt).row2);
    crate::vec3::ops::lemma_dot_congruence(mt.row2, mt.row2, adj.row2, transpose(adj_mt).row2);

    // (2,0): dot(adj.row2, mt.row0) ≡ ... ≡ mat_mul(mt,adj_mt).row0.z ≡ 0
    crate::vec3::ops::lemma_dot_commutative(adj.row2, mt.row0);
    T::axiom_eqv_transitive(
        dot(adj.row2, mt.row0), dot(mt.row0, adj.row2), dot(mt.row0, transpose(adj_mt).row2),
    );
    T::axiom_eqv_transitive(
        dot(adj.row2, mt.row0), dot(mt.row0, transpose(adj_mt).row2), T::zero(),
    );

    // (2,1): dot(adj.row2, mt.row1) ≡ ... ≡ mat_mul(mt,adj_mt).row1.z ≡ 0
    crate::vec3::ops::lemma_dot_commutative(adj.row2, mt.row1);
    T::axiom_eqv_transitive(
        dot(adj.row2, mt.row1), dot(mt.row1, adj.row2), dot(mt.row1, transpose(adj_mt).row2),
    );
    T::axiom_eqv_transitive(
        dot(adj.row2, mt.row1), dot(mt.row1, transpose(adj_mt).row2), T::zero(),
    );

    // (2,2): dot(adj.row2, mt.row2) ≡ dot(mt.row2, t_adj_mt.row2)
    //        = mat_mul(mt, adj_mt).row2.z ≡ det(mt) ≡ det(m)
    crate::vec3::ops::lemma_dot_commutative(adj.row2, mt.row2);
    T::axiom_eqv_transitive(
        dot(adj.row2, mt.row2), dot(mt.row2, adj.row2), dot(mt.row2, transpose(adj_mt).row2),
    );
    T::axiom_eqv_transitive(
        dot(adj.row2, mt.row2), dot(mt.row2, transpose(adj_mt).row2), det(mt),
    );
    T::axiom_eqv_transitive(dot(adj.row2, mt.row2), det(mt), det(m));
}

// ---------------------------------------------------------------------------
// Inverse proofs
// ---------------------------------------------------------------------------

/// m * inverse(m) ≡ I
pub proof fn lemma_inverse_right<T: Field>(m: Mat3x3<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        mat_mul(m, inverse(m)).row0.eqv(identity::<T>().row0),
        mat_mul(m, inverse(m)).row1.eqv(identity::<T>().row1),
        mat_mul(m, inverse(m)).row2.eqv(identity::<T>().row2),
{
    let d = det(m);
    let d_inv = d.recip();
    let adj = adjugate(m);
    let inv = inverse(m);
    let t_inv = transpose(inv);
    let t_adj = transpose(adj);

    // transpose(inv).row_j = scale(d_inv, transpose(adj).row_j) definitionally.
    // So dot(m.row_i, t_inv.row_j) = dot(m.row_i, scale(d_inv, t_adj.row_j))
    //   ≡ d_inv * dot(m.row_i, t_adj.row_j)   [dot_scale_right]
    //   = d_inv * mat_mul(m, adj)_{i,j}

    lemma_mat_mul_adjugate_right(m);

    // Factor d_inv out of each of 9 dot products
    crate::vec3::ops::lemma_dot_scale_right(d_inv, m.row0, t_adj.row0);
    crate::vec3::ops::lemma_dot_scale_right(d_inv, m.row0, t_adj.row1);
    crate::vec3::ops::lemma_dot_scale_right(d_inv, m.row0, t_adj.row2);
    crate::vec3::ops::lemma_dot_scale_right(d_inv, m.row1, t_adj.row0);
    crate::vec3::ops::lemma_dot_scale_right(d_inv, m.row1, t_adj.row1);
    crate::vec3::ops::lemma_dot_scale_right(d_inv, m.row1, t_adj.row2);
    crate::vec3::ops::lemma_dot_scale_right(d_inv, m.row2, t_adj.row0);
    crate::vec3::ops::lemma_dot_scale_right(d_inv, m.row2, t_adj.row1);
    crate::vec3::ops::lemma_dot_scale_right(d_inv, m.row2, t_adj.row2);

    // d_inv * d ≡ 1
    field_lemmas::lemma_mul_recip_left::<T>(d);

    // --- Diagonal entries: d_inv * det(m) ≡ 1 ---

    // (0,0)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row0, t_adj.row0), d);
    T::axiom_eqv_transitive(dot(m.row0, t_inv.row0), d_inv.mul(dot(m.row0, t_adj.row0)), d_inv.mul(d));
    T::axiom_eqv_transitive(dot(m.row0, t_inv.row0), d_inv.mul(d), T::one());

    // (1,1)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row1, t_adj.row1), d);
    T::axiom_eqv_transitive(dot(m.row1, t_inv.row1), d_inv.mul(dot(m.row1, t_adj.row1)), d_inv.mul(d));
    T::axiom_eqv_transitive(dot(m.row1, t_inv.row1), d_inv.mul(d), T::one());

    // (2,2)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row2, t_adj.row2), d);
    T::axiom_eqv_transitive(dot(m.row2, t_inv.row2), d_inv.mul(dot(m.row2, t_adj.row2)), d_inv.mul(d));
    T::axiom_eqv_transitive(dot(m.row2, t_inv.row2), d_inv.mul(d), T::one());

    // --- Off-diagonal entries: d_inv * 0 ≡ 0 ---

    // (0,1)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row0, t_adj.row1), T::zero());
    T::axiom_eqv_transitive(dot(m.row0, t_inv.row1), d_inv.mul(dot(m.row0, t_adj.row1)), d_inv.mul(T::zero()));
    T::axiom_mul_zero_right(d_inv);
    T::axiom_eqv_transitive(dot(m.row0, t_inv.row1), d_inv.mul(T::zero()), T::zero());

    // (0,2)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row0, t_adj.row2), T::zero());
    T::axiom_eqv_transitive(dot(m.row0, t_inv.row2), d_inv.mul(dot(m.row0, t_adj.row2)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row0, t_inv.row2), d_inv.mul(T::zero()), T::zero());

    // (1,0)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row1, t_adj.row0), T::zero());
    T::axiom_eqv_transitive(dot(m.row1, t_inv.row0), d_inv.mul(dot(m.row1, t_adj.row0)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row1, t_inv.row0), d_inv.mul(T::zero()), T::zero());

    // (1,2)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row1, t_adj.row2), T::zero());
    T::axiom_eqv_transitive(dot(m.row1, t_inv.row2), d_inv.mul(dot(m.row1, t_adj.row2)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row1, t_inv.row2), d_inv.mul(T::zero()), T::zero());

    // (2,0)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row2, t_adj.row0), T::zero());
    T::axiom_eqv_transitive(dot(m.row2, t_inv.row0), d_inv.mul(dot(m.row2, t_adj.row0)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row2, t_inv.row0), d_inv.mul(T::zero()), T::zero());

    // (2,1)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row2, t_adj.row1), T::zero());
    T::axiom_eqv_transitive(dot(m.row2, t_inv.row1), d_inv.mul(dot(m.row2, t_adj.row1)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row2, t_inv.row1), d_inv.mul(T::zero()), T::zero());
}

/// inverse(m) * m ≡ I
pub proof fn lemma_inverse_left<T: Field>(m: Mat3x3<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        mat_mul(inverse(m), m).row0.eqv(identity::<T>().row0),
        mat_mul(inverse(m), m).row1.eqv(identity::<T>().row1),
        mat_mul(inverse(m), m).row2.eqv(identity::<T>().row2),
{
    let d = det(m);
    let d_inv = d.recip();
    let adj = adjugate(m);
    let inv = inverse(m);
    let mt = transpose(m);

    // inv.row_i = scale(d_inv, adj.row_i)
    // So dot(inv.row_i, mt.row_j) = dot(scale(d_inv, adj.row_i), mt.row_j)
    //   ≡ d_inv * dot(adj.row_i, mt.row_j)   [dot_scale_left]
    //   = d_inv * mat_mul(adj, m)_{i,j}

    lemma_mat_mul_adjugate_left(m);

    // Factor d_inv out of each of 9 dot products
    crate::vec3::ops::lemma_dot_scale_left(d_inv, adj.row0, mt.row0);
    crate::vec3::ops::lemma_dot_scale_left(d_inv, adj.row0, mt.row1);
    crate::vec3::ops::lemma_dot_scale_left(d_inv, adj.row0, mt.row2);
    crate::vec3::ops::lemma_dot_scale_left(d_inv, adj.row1, mt.row0);
    crate::vec3::ops::lemma_dot_scale_left(d_inv, adj.row1, mt.row1);
    crate::vec3::ops::lemma_dot_scale_left(d_inv, adj.row1, mt.row2);
    crate::vec3::ops::lemma_dot_scale_left(d_inv, adj.row2, mt.row0);
    crate::vec3::ops::lemma_dot_scale_left(d_inv, adj.row2, mt.row1);
    crate::vec3::ops::lemma_dot_scale_left(d_inv, adj.row2, mt.row2);

    // d_inv * d ≡ 1
    field_lemmas::lemma_mul_recip_left::<T>(d);

    // --- Diagonal entries: d_inv * det(m) ≡ 1 ---

    // (0,0)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row0, mt.row0), d);
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row0), d_inv.mul(dot(adj.row0, mt.row0)), d_inv.mul(d));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row0), d_inv.mul(d), T::one());

    // (1,1)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row1, mt.row1), d);
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row1), d_inv.mul(dot(adj.row1, mt.row1)), d_inv.mul(d));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row1), d_inv.mul(d), T::one());

    // (2,2)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row2, mt.row2), d);
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row2), d_inv.mul(dot(adj.row2, mt.row2)), d_inv.mul(d));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row2), d_inv.mul(d), T::one());

    // --- Off-diagonal entries: d_inv * 0 ≡ 0 ---

    // (0,1)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row0, mt.row1), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row1), d_inv.mul(dot(adj.row0, mt.row1)), d_inv.mul(T::zero()));
    T::axiom_mul_zero_right(d_inv);
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row1), d_inv.mul(T::zero()), T::zero());

    // (0,2)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row0, mt.row2), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row2), d_inv.mul(dot(adj.row0, mt.row2)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row2), d_inv.mul(T::zero()), T::zero());

    // (1,0)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row1, mt.row0), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row0), d_inv.mul(dot(adj.row1, mt.row0)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row0), d_inv.mul(T::zero()), T::zero());

    // (1,2)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row1, mt.row2), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row2), d_inv.mul(dot(adj.row1, mt.row2)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row2), d_inv.mul(T::zero()), T::zero());

    // (2,0)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row2, mt.row0), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row0), d_inv.mul(dot(adj.row2, mt.row0)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row0), d_inv.mul(T::zero()), T::zero());

    // (2,1)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row2, mt.row1), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row1), d_inv.mul(dot(adj.row2, mt.row1)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row1), d_inv.mul(T::zero()), T::zero());
}

// ---------------------------------------------------------------------------
// Mat-vec-mul associativity
// ---------------------------------------------------------------------------

/// Helper: s * dot(u, v) ≡ (s*u.x)*v.x + (s*u.y)*v.y + (s*u.z)*v.z
/// i.e., distribute s into each term of the dot product and reassociate.
proof fn lemma_distribute_scalar_dot3<T: Ring>(s: T, u: Vec3<T>, v: Vec3<T>)
    ensures
        s.mul(dot(u, v)).eqv(
            s.mul(u.x).mul(v.x).add(s.mul(u.y).mul(v.y)).add(s.mul(u.z).mul(v.z))
        ),
{
    // dot(u, v) = (u.x*v.x + u.y*v.y) + u.z*v.z
    // s * ((u.x*v.x + u.y*v.y) + u.z*v.z) ≡ s*(u.x*v.x + u.y*v.y) + s*(u.z*v.z)
    T::axiom_mul_distributes_left(s, u.x.mul(v.x).add(u.y.mul(v.y)), u.z.mul(v.z));

    // s*(u.x*v.x + u.y*v.y) ≡ s*(u.x*v.x) + s*(u.y*v.y)
    T::axiom_mul_distributes_left(s, u.x.mul(v.x), u.y.mul(v.y));

    // s*(u.i*v.i) ≡ (s*u.i)*v.i  for each i
    T::axiom_mul_associative(s, u.x, v.x);
    T::axiom_eqv_symmetric(s.mul(u.x).mul(v.x), s.mul(u.x.mul(v.x)));
    T::axiom_mul_associative(s, u.y, v.y);
    T::axiom_eqv_symmetric(s.mul(u.y).mul(v.y), s.mul(u.y.mul(v.y)));
    T::axiom_mul_associative(s, u.z, v.z);
    T::axiom_eqv_symmetric(s.mul(u.z).mul(v.z), s.mul(u.z.mul(v.z)));

    // Combine inner: s*(u.x*v.x) + s*(u.y*v.y) ≡ (s*u.x)*v.x + (s*u.y)*v.y
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(u.x.mul(v.x)), s.mul(u.x).mul(v.x),
        s.mul(u.y.mul(v.y)), s.mul(u.y).mul(v.y),
    );
    // Chain inner: s*(u.x*v.x + u.y*v.y) ≡ (s*u.x)*v.x + (s*u.y)*v.y
    T::axiom_eqv_transitive(
        s.mul(u.x.mul(v.x).add(u.y.mul(v.y))),
        s.mul(u.x.mul(v.x)).add(s.mul(u.y.mul(v.y))),
        s.mul(u.x).mul(v.x).add(s.mul(u.y).mul(v.y)),
    );

    // Combine outer: (...) + s*(u.z*v.z) ≡ (...) + (s*u.z)*v.z
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(u.x.mul(v.x).add(u.y.mul(v.y))),
        s.mul(u.x).mul(v.x).add(s.mul(u.y).mul(v.y)),
        s.mul(u.z.mul(v.z)),
        s.mul(u.z).mul(v.z),
    );
    // Chain outer: s * dot(u, v) ≡ (s*u.x)*v.x + (s*u.y)*v.y + (s*u.z)*v.z
    T::axiom_eqv_transitive(
        s.mul(dot(u, v)),
        s.mul(u.x.mul(v.x).add(u.y.mul(v.y))).add(s.mul(u.z.mul(v.z))),
        s.mul(u.x).mul(v.x).add(s.mul(u.y).mul(v.y)).add(s.mul(u.z).mul(v.z)),
    );
}

/// Rearrange 9 terms from row-major to column-major grouping.
/// ((a0+a1)+a2) + ((b0+b1)+b2)) + ((c0+c1)+c2)
/// ≡ ((a0+b0)+c0) + ((a1+b1)+c1)) + ((a2+b2)+c2)
proof fn lemma_add_rearrange_3x3<T: Ring>(
    a0: T, a1: T, a2: T,
    b0: T, b1: T, b2: T,
    c0: T, c1: T, c2: T,
)
    ensures
        a0.add(a1).add(a2).add(b0.add(b1).add(b2)).add(c0.add(c1).add(c2)).eqv(
            a0.add(b0).add(c0).add(a1.add(b1).add(c1)).add(a2.add(b2).add(c2))
        ),
{
    let p = a0.add(a1).add(a2);
    let q = b0.add(b1).add(b2);
    let r = c0.add(c1).add(c2);

    // Step 1: rearrange_2x2(a0+a1, a2, b0+b1, b2)
    //   P + Q ≡ ((a0+a1)+(b0+b1)) + (a2+b2)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a0.add(a1), a2, b0.add(b1), b2);

    // Step 2: rearrange_2x2(a0, a1, b0, b1)
    //   (a0+a1)+(b0+b1) ≡ (a0+b0)+(a1+b1)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a0, a1, b0, b1);

    // Step 3: substitute step 2 into step 1
    T::axiom_add_congruence_left(
        a0.add(a1).add(b0.add(b1)), a0.add(b0).add(a1.add(b1)), a2.add(b2),
    );
    T::axiom_eqv_transitive(
        p.add(q),
        a0.add(a1).add(b0.add(b1)).add(a2.add(b2)),
        a0.add(b0).add(a1.add(b1)).add(a2.add(b2)),
    );

    // Step 4: add R to both sides
    T::axiom_add_congruence_left(
        p.add(q), a0.add(b0).add(a1.add(b1)).add(a2.add(b2)), r,
    );

    // Step 5: rearrange_2x2(a0+b0 + a1+b1, a2+b2, c0+c1, c2)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a0.add(b0).add(a1.add(b1)), a2.add(b2), c0.add(c1), c2,
    );

    // Step 6: rearrange_2x2(a0+b0, a1+b1, c0, c1)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a0.add(b0), a1.add(b1), c0, c1);

    // Step 7: substitute step 6 into step 5
    T::axiom_add_congruence_left(
        a0.add(b0).add(a1.add(b1)).add(c0.add(c1)),
        a0.add(b0).add(c0).add(a1.add(b1).add(c1)),
        a2.add(b2).add(c2),
    );
    T::axiom_eqv_transitive(
        a0.add(b0).add(a1.add(b1)).add(a2.add(b2)).add(r),
        a0.add(b0).add(a1.add(b1)).add(c0.add(c1)).add(a2.add(b2).add(c2)),
        a0.add(b0).add(c0).add(a1.add(b1).add(c1)).add(a2.add(b2).add(c2)),
    );

    // Chain: (P+Q)+R ≡ step4_result ≡ step7_result
    T::axiom_eqv_transitive(
        p.add(q).add(r),
        a0.add(b0).add(a1.add(b1)).add(a2.add(b2)).add(r),
        a0.add(b0).add(c0).add(a1.add(b1).add(c1)).add(a2.add(b2).add(c2)),
    );
}

/// Factor 3 additive terms over a common right factor:
/// (p*z + q*z) + r*z ≡ ((p+q)+r)*z
proof fn lemma_factor_3<T: Ring>(p: T, q: T, r: T, z: T)
    ensures
        p.mul(z).add(q.mul(z)).add(r.mul(z)).eqv(p.add(q).add(r).mul(z)),
{
    ring_lemmas::lemma_mul_distributes_right::<T>(p, q, z);
    T::axiom_eqv_symmetric(p.add(q).mul(z), p.mul(z).add(q.mul(z)));
    ring_lemmas::lemma_mul_distributes_right::<T>(p.add(q), r, z);
    T::axiom_eqv_symmetric(p.add(q).add(r).mul(z), p.add(q).mul(z).add(r.mul(z)));
    T::axiom_add_congruence_left(p.mul(z).add(q.mul(z)), p.add(q).mul(z), r.mul(z));
    T::axiom_eqv_transitive(
        p.mul(z).add(q.mul(z)).add(r.mul(z)),
        p.add(q).mul(z).add(r.mul(z)),
        p.add(q).add(r).mul(z),
    );
}

/// 3-term additive congruence: if a1≡a2, b1≡b2, c1≡c2, then (a1+b1)+c1 ≡ (a2+b2)+c2
proof fn lemma_add_congruence_3<T: Ring>(a1: T, a2: T, b1: T, b2: T, c1: T, c2: T)
    requires a1.eqv(a2), b1.eqv(b2), c1.eqv(c2),
    ensures a1.add(b1).add(c1).eqv(a2.add(b2).add(c2)),
{
    additive_group_lemmas::lemma_add_congruence::<T>(a1, a2, b1, b2);
    additive_group_lemmas::lemma_add_congruence::<T>(a1.add(b1), a2.add(b2), c1, c2);
}

/// Helper: for any row vector ai and matrix b,
/// dot(ai, mat_vec_mul(b, v)) ≡ dot(ai, bt.col0)*v.x + dot(ai, bt.col1)*v.y + dot(ai, bt.col2)*v.z
proof fn lemma_dot_mat_vec_mul_row<T: Ring>(ai: Vec3<T>, b: Mat3x3<T>, v: Vec3<T>)
    ensures
        dot(ai, mat_vec_mul(b, v)).eqv(
            dot(ai, transpose(b).row0).mul(v.x)
                .add(dot(ai, transpose(b).row1).mul(v.y))
                .add(dot(ai, transpose(b).row2).mul(v.z))
        ),
{
    // Step 1: distribute each scalar into its dot product
    lemma_distribute_scalar_dot3(ai.x, b.row0, v);
    lemma_distribute_scalar_dot3(ai.y, b.row1, v);
    lemma_distribute_scalar_dot3(ai.z, b.row2, v);

    // Step 2: combine all three distributed forms
    lemma_add_congruence_3::<T>(
        ai.x.mul(dot(b.row0, v)),
        ai.x.mul(b.row0.x).mul(v.x).add(ai.x.mul(b.row0.y).mul(v.y)).add(ai.x.mul(b.row0.z).mul(v.z)),
        ai.y.mul(dot(b.row1, v)),
        ai.y.mul(b.row1.x).mul(v.x).add(ai.y.mul(b.row1.y).mul(v.y)).add(ai.y.mul(b.row1.z).mul(v.z)),
        ai.z.mul(dot(b.row2, v)),
        ai.z.mul(b.row2.x).mul(v.x).add(ai.z.mul(b.row2.y).mul(v.y)).add(ai.z.mul(b.row2.z).mul(v.z)),
    );

    // Step 3: rearrange from row-major to column-major grouping
    lemma_add_rearrange_3x3(
        ai.x.mul(b.row0.x).mul(v.x), ai.x.mul(b.row0.y).mul(v.y), ai.x.mul(b.row0.z).mul(v.z),
        ai.y.mul(b.row1.x).mul(v.x), ai.y.mul(b.row1.y).mul(v.y), ai.y.mul(b.row1.z).mul(v.z),
        ai.z.mul(b.row2.x).mul(v.x), ai.z.mul(b.row2.y).mul(v.y), ai.z.mul(b.row2.z).mul(v.z),
    );

    // Step 4: factor v.x, v.y, v.z from each column-group
    lemma_factor_3(ai.x.mul(b.row0.x), ai.y.mul(b.row1.x), ai.z.mul(b.row2.x), v.x);
    lemma_factor_3(ai.x.mul(b.row0.y), ai.y.mul(b.row1.y), ai.z.mul(b.row2.y), v.y);
    lemma_factor_3(ai.x.mul(b.row0.z), ai.y.mul(b.row1.z), ai.z.mul(b.row2.z), v.z);

    // Step 5: combine the factored groups
    lemma_add_congruence_3::<T>(
        ai.x.mul(b.row0.x).mul(v.x).add(ai.y.mul(b.row1.x).mul(v.x)).add(ai.z.mul(b.row2.x).mul(v.x)),
        ai.x.mul(b.row0.x).add(ai.y.mul(b.row1.x)).add(ai.z.mul(b.row2.x)).mul(v.x),
        ai.x.mul(b.row0.y).mul(v.y).add(ai.y.mul(b.row1.y).mul(v.y)).add(ai.z.mul(b.row2.y).mul(v.y)),
        ai.x.mul(b.row0.y).add(ai.y.mul(b.row1.y)).add(ai.z.mul(b.row2.y)).mul(v.y),
        ai.x.mul(b.row0.z).mul(v.z).add(ai.y.mul(b.row1.z).mul(v.z)).add(ai.z.mul(b.row2.z).mul(v.z)),
        ai.x.mul(b.row0.z).add(ai.y.mul(b.row1.z)).add(ai.z.mul(b.row2.z)).mul(v.z),
    );

    // Step 6: chain lhs ≡ dist ≡ rear ≡ fact
    let lhs = ai.x.mul(dot(b.row0, v))
        .add(ai.y.mul(dot(b.row1, v)))
        .add(ai.z.mul(dot(b.row2, v)));
    let dist = ai.x.mul(b.row0.x).mul(v.x).add(ai.x.mul(b.row0.y).mul(v.y)).add(ai.x.mul(b.row0.z).mul(v.z))
        .add(ai.y.mul(b.row1.x).mul(v.x).add(ai.y.mul(b.row1.y).mul(v.y)).add(ai.y.mul(b.row1.z).mul(v.z)))
        .add(ai.z.mul(b.row2.x).mul(v.x).add(ai.z.mul(b.row2.y).mul(v.y)).add(ai.z.mul(b.row2.z).mul(v.z)));
    let rear = ai.x.mul(b.row0.x).mul(v.x).add(ai.y.mul(b.row1.x).mul(v.x)).add(ai.z.mul(b.row2.x).mul(v.x))
        .add(ai.x.mul(b.row0.y).mul(v.y).add(ai.y.mul(b.row1.y).mul(v.y)).add(ai.z.mul(b.row2.y).mul(v.y)))
        .add(ai.x.mul(b.row0.z).mul(v.z).add(ai.y.mul(b.row1.z).mul(v.z)).add(ai.z.mul(b.row2.z).mul(v.z)));
    let fact = ai.x.mul(b.row0.x).add(ai.y.mul(b.row1.x)).add(ai.z.mul(b.row2.x)).mul(v.x)
        .add(ai.x.mul(b.row0.y).add(ai.y.mul(b.row1.y)).add(ai.z.mul(b.row2.y)).mul(v.y))
        .add(ai.x.mul(b.row0.z).add(ai.y.mul(b.row1.z)).add(ai.z.mul(b.row2.z)).mul(v.z));

    T::axiom_eqv_transitive(lhs, dist, rear);
    T::axiom_eqv_transitive(lhs, rear, fact);
}

/// mat_vec_mul(a, mat_vec_mul(b, v)) ≡ mat_vec_mul(mat_mul(a, b), v)
pub proof fn lemma_mat_vec_mul_mat_mul<T: Ring>(a: Mat3x3<T>, b: Mat3x3<T>, v: Vec3<T>)
    ensures
        mat_vec_mul(a, mat_vec_mul(b, v)).eqv(mat_vec_mul(mat_mul(a, b), v)),
{
    lemma_dot_mat_vec_mul_row(a.row0, b, v);
    lemma_dot_mat_vec_mul_row(a.row1, b, v);
    lemma_dot_mat_vec_mul_row(a.row2, b, v);
}

// ---------------------------------------------------------------------------
// Det multiplicative helpers
// ---------------------------------------------------------------------------

/// Expand triple with 3-term scaled sum in first arg:
/// triple(s0*r0 + s1*r1 + s2*r2, p, q) ≡ s0*T(r0,p,q) + s1*T(r1,p,q) + s2*T(r2,p,q)
proof fn lemma_triple_expand_arg1_3<T: Ring>(
    s0: T, r0: Vec3<T>, s1: T, r1: Vec3<T>, s2: T, r2: Vec3<T>,
    p: Vec3<T>, q: Vec3<T>,
)
    ensures
        triple(
            scale(s0, r0).add(scale(s1, r1)).add(scale(s2, r2)),
            p, q,
        ).eqv(
            s0.mul(triple(r0, p, q))
              .add(s1.mul(triple(r1, p, q)))
              .add(s2.mul(triple(r2, p, q)))
        ),
{
    let x = scale(s0, r0);
    let y = scale(s1, r1);
    let z = scale(s2, r2);

    // triple((x+y)+z, p, q) ≡ triple(x+y, p, q) + triple(z, p, q)
    crate::vec3::ops::lemma_triple_linear_first(x.add(y), z, p, q);
    // triple(x+y, p, q) ≡ triple(x, p, q) + triple(y, p, q)
    crate::vec3::ops::lemma_triple_linear_first(x, y, p, q);

    // Factor out scales
    crate::vec3::ops::lemma_triple_scale_first(s0, r0, p, q);
    crate::vec3::ops::lemma_triple_scale_first(s1, r1, p, q);
    crate::vec3::ops::lemma_triple_scale_first(s2, r2, p, q);

    let t0 = triple(r0, p, q);
    let t1 = triple(r1, p, q);
    let t2 = triple(r2, p, q);

    // triple(x+y,p,q) ≡ triple(x,p,q) + triple(y,p,q) ≡ s0*t0 + s1*t1
    T::axiom_add_congruence_left(triple(x, p, q), s0.mul(t0), triple(y, p, q));
    additive_group_lemmas::lemma_add_congruence_right(s0.mul(t0), triple(y, p, q), s1.mul(t1));
    T::axiom_eqv_transitive(
        triple(x, p, q).add(triple(y, p, q)),
        s0.mul(t0).add(triple(y, p, q)),
        s0.mul(t0).add(s1.mul(t1)),
    );
    // triple(x+y,p,q) ≡ s0*t0 + s1*t1
    T::axiom_eqv_transitive(
        triple(x.add(y), p, q),
        triple(x, p, q).add(triple(y, p, q)),
        s0.mul(t0).add(s1.mul(t1)),
    );

    // Now chain: triple((x+y)+z,p,q) ≡ triple(x+y,p,q) + triple(z,p,q) ≡ (s0*t0+s1*t1) + s2*t2
    T::axiom_add_congruence_left(
        triple(x.add(y), p, q), s0.mul(t0).add(s1.mul(t1)),
        triple(z, p, q),
    );
    additive_group_lemmas::lemma_add_congruence_right(
        s0.mul(t0).add(s1.mul(t1)),
        triple(z, p, q), s2.mul(t2),
    );
    T::axiom_eqv_transitive(
        triple(x.add(y), p, q).add(triple(z, p, q)),
        s0.mul(t0).add(s1.mul(t1)).add(triple(z, p, q)),
        s0.mul(t0).add(s1.mul(t1)).add(s2.mul(t2)),
    );
    T::axiom_eqv_transitive(
        triple(x.add(y).add(z), p, q),
        triple(x.add(y), p, q).add(triple(z, p, q)),
        s0.mul(t0).add(s1.mul(t1)).add(s2.mul(t2)),
    );
}

/// Same expansion for second arg
proof fn lemma_triple_expand_arg2_3<T: Ring>(
    p: Vec3<T>,
    s0: T, r0: Vec3<T>, s1: T, r1: Vec3<T>, s2: T, r2: Vec3<T>,
    q: Vec3<T>,
)
    ensures
        triple(
            p,
            scale(s0, r0).add(scale(s1, r1)).add(scale(s2, r2)),
            q,
        ).eqv(
            s0.mul(triple(p, r0, q))
              .add(s1.mul(triple(p, r1, q)))
              .add(s2.mul(triple(p, r2, q)))
        ),
{
    let x = scale(s0, r0);
    let y = scale(s1, r1);
    let z = scale(s2, r2);

    crate::vec3::ops::lemma_triple_linear_second(p, x.add(y), z, q);
    crate::vec3::ops::lemma_triple_linear_second(p, x, y, q);
    crate::vec3::ops::lemma_triple_scale_second(s0, p, r0, q);
    crate::vec3::ops::lemma_triple_scale_second(s1, p, r1, q);
    crate::vec3::ops::lemma_triple_scale_second(s2, p, r2, q);

    let t0 = triple(p, r0, q);
    let t1 = triple(p, r1, q);
    let t2 = triple(p, r2, q);

    T::axiom_add_congruence_left(triple(p, x, q), s0.mul(t0), triple(p, y, q));
    additive_group_lemmas::lemma_add_congruence_right(s0.mul(t0), triple(p, y, q), s1.mul(t1));
    T::axiom_eqv_transitive(
        triple(p, x, q).add(triple(p, y, q)),
        s0.mul(t0).add(triple(p, y, q)),
        s0.mul(t0).add(s1.mul(t1)),
    );
    T::axiom_eqv_transitive(
        triple(p, x.add(y), q),
        triple(p, x, q).add(triple(p, y, q)),
        s0.mul(t0).add(s1.mul(t1)),
    );

    T::axiom_add_congruence_left(
        triple(p, x.add(y), q), s0.mul(t0).add(s1.mul(t1)),
        triple(p, z, q),
    );
    additive_group_lemmas::lemma_add_congruence_right(
        s0.mul(t0).add(s1.mul(t1)),
        triple(p, z, q), s2.mul(t2),
    );
    T::axiom_eqv_transitive(
        triple(p, x.add(y), q).add(triple(p, z, q)),
        s0.mul(t0).add(s1.mul(t1)).add(triple(p, z, q)),
        s0.mul(t0).add(s1.mul(t1)).add(s2.mul(t2)),
    );
    T::axiom_eqv_transitive(
        triple(p, x.add(y).add(z), q),
        triple(p, x.add(y), q).add(triple(p, z, q)),
        s0.mul(t0).add(s1.mul(t1)).add(s2.mul(t2)),
    );
}

/// Same expansion for third arg
proof fn lemma_triple_expand_arg3_3<T: Ring>(
    p: Vec3<T>,
    q: Vec3<T>,
    s0: T, r0: Vec3<T>, s1: T, r1: Vec3<T>, s2: T, r2: Vec3<T>,
)
    ensures
        triple(
            p, q,
            scale(s0, r0).add(scale(s1, r1)).add(scale(s2, r2)),
        ).eqv(
            s0.mul(triple(p, q, r0))
              .add(s1.mul(triple(p, q, r1)))
              .add(s2.mul(triple(p, q, r2)))
        ),
{
    let x = scale(s0, r0);
    let y = scale(s1, r1);
    let z = scale(s2, r2);

    crate::vec3::ops::lemma_triple_linear_third(p, q, x.add(y), z);
    crate::vec3::ops::lemma_triple_linear_third(p, q, x, y);
    crate::vec3::ops::lemma_triple_scale_third(s0, p, q, r0);
    crate::vec3::ops::lemma_triple_scale_third(s1, p, q, r1);
    crate::vec3::ops::lemma_triple_scale_third(s2, p, q, r2);

    let t0 = triple(p, q, r0);
    let t1 = triple(p, q, r1);
    let t2 = triple(p, q, r2);

    T::axiom_add_congruence_left(triple(p, q, x), s0.mul(t0), triple(p, q, y));
    additive_group_lemmas::lemma_add_congruence_right(s0.mul(t0), triple(p, q, y), s1.mul(t1));
    T::axiom_eqv_transitive(
        triple(p, q, x).add(triple(p, q, y)),
        s0.mul(t0).add(triple(p, q, y)),
        s0.mul(t0).add(s1.mul(t1)),
    );
    T::axiom_eqv_transitive(
        triple(p, q, x.add(y)),
        triple(p, q, x).add(triple(p, q, y)),
        s0.mul(t0).add(s1.mul(t1)),
    );

    T::axiom_add_congruence_left(
        triple(p, q, x.add(y)), s0.mul(t0).add(s1.mul(t1)),
        triple(p, q, z),
    );
    additive_group_lemmas::lemma_add_congruence_right(
        s0.mul(t0).add(s1.mul(t1)),
        triple(p, q, z), s2.mul(t2),
    );
    T::axiom_eqv_transitive(
        triple(p, q, x.add(y)).add(triple(p, q, z)),
        s0.mul(t0).add(s1.mul(t1)).add(triple(p, q, z)),
        s0.mul(t0).add(s1.mul(t1)).add(s2.mul(t2)),
    );
    T::axiom_eqv_transitive(
        triple(p, q, x.add(y).add(z)),
        triple(p, q, x.add(y)).add(triple(p, q, z)),
        s0.mul(t0).add(s1.mul(t1)).add(s2.mul(t2)),
    );
}

/// If x ≡ 0 then s*x ≡ 0
proof fn lemma_mul_zero_by_eqv<T: Ring>(s: T, x: T)
    requires x.eqv(T::zero()),
    ensures s.mul(x).eqv(T::zero()),
{
    ring_lemmas::lemma_mul_congruence_right(s, x, T::zero());
    T::axiom_mul_zero_right(s);
    T::axiom_eqv_transitive(s.mul(x), s.mul(T::zero()), T::zero());
}

/// Kill first of 3 terms: if a ≡ 0, then (a + b) + c ≡ b + c
proof fn lemma_sum3_kill_first<T: Ring>(a: T, b: T, c: T)
    requires a.eqv(T::zero()),
    ensures a.add(b).add(c).eqv(b.add(c)),
{
    // a ≡ 0 → a+b ≡ 0+b ≡ b
    T::axiom_add_congruence_left(a, T::zero(), b);
    additive_group_lemmas::lemma_add_zero_left(b);
    T::axiom_eqv_transitive(a.add(b), T::zero().add(b), b);
    // a+b ≡ b → (a+b)+c ≡ b+c
    T::axiom_add_congruence_left(a.add(b), b, c);
}

/// Kill second of 3 terms: if b ≡ 0, then (a + b) + c ≡ a + c
proof fn lemma_sum3_kill_second<T: Ring>(a: T, b: T, c: T)
    requires b.eqv(T::zero()),
    ensures a.add(b).add(c).eqv(a.add(c)),
{
    additive_group_lemmas::lemma_add_congruence_right(a, b, T::zero());
    T::axiom_add_zero_right(a);
    T::axiom_eqv_transitive(a.add(b), a.add(T::zero()), a);
    T::axiom_add_congruence_left(a.add(b), a, c);
}

/// Kill third of 3 terms: if c ≡ 0, then (a + b) + c ≡ a + b
proof fn lemma_sum3_kill_third<T: Ring>(a: T, b: T, c: T)
    requires c.eqv(T::zero()),
    ensures a.add(b).add(c).eqv(a.add(b)),
{
    additive_group_lemmas::lemma_add_congruence_right(a.add(b), c, T::zero());
    T::axiom_add_zero_right(a.add(b));
    T::axiom_eqv_transitive(a.add(b).add(c), a.add(b).add(T::zero()), a.add(b));
}

/// Kill first and third: if a ≡ 0, c ≡ 0, then (a + b) + c ≡ b
proof fn lemma_sum3_kill_first_third<T: Ring>(a: T, b: T, c: T)
    requires a.eqv(T::zero()), c.eqv(T::zero()),
    ensures a.add(b).add(c).eqv(b),
{
    lemma_sum3_kill_first(a, b, c);
    // b+c where c ≡ 0 → b+c ≡ b
    additive_group_lemmas::lemma_add_congruence_right(b, c, T::zero());
    T::axiom_add_zero_right(b);
    T::axiom_eqv_transitive(b.add(c), b.add(T::zero()), b);
    T::axiom_eqv_transitive(a.add(b).add(c), b.add(c), b);
}

/// Kill first and second: if a ≡ 0, b ≡ 0, then (a + b) + c ≡ c
proof fn lemma_sum3_kill_first_second<T: Ring>(a: T, b: T, c: T)
    requires a.eqv(T::zero()), b.eqv(T::zero()),
    ensures a.add(b).add(c).eqv(c),
{
    lemma_sum3_kill_first(a, b, c);
    // b+c where b ≡ 0 → b+c ≡ 0+c ≡ c
    T::axiom_add_congruence_left(b, T::zero(), c);
    additive_group_lemmas::lemma_add_zero_left(c);
    T::axiom_eqv_transitive(b.add(c), T::zero().add(c), c);
    T::axiom_eqv_transitive(a.add(b).add(c), b.add(c), c);
}

/// Kill second and third: if b ≡ 0, c ≡ 0, then (a + b) + c ≡ a
proof fn lemma_sum3_kill_second_third<T: Ring>(a: T, b: T, c: T)
    requires b.eqv(T::zero()), c.eqv(T::zero()),
    ensures a.add(b).add(c).eqv(a),
{
    lemma_sum3_kill_second(a, b, c);
    // a+c where c ≡ 0 → a+c ≡ a
    additive_group_lemmas::lemma_add_congruence_right(a, c, T::zero());
    T::axiom_add_zero_right(a);
    T::axiom_eqv_transitive(a.add(c), a.add(T::zero()), a);
    T::axiom_eqv_transitive(a.add(b).add(c), a.add(c), a);
}

/// Column 0 of det multiplicative: triple(b0, ABr1, ABr2) ≡ cross(a1,a2).x * det(b)
proof fn lemma_det_mul_col0<T: Ring>(a: Mat3x3<T>, b: Mat3x3<T>)
    ensures triple(b.row0, mat_mul(a,b).row1, mat_mul(a,b).row2)
            .eqv(cross(a.row1, a.row2).x.mul(det(b))),
{
    let a1 = a.row1; let a2 = a.row2;
    let (b0, b1, b2) = (b.row0, b.row1, b.row2);
    let ab = mat_mul(a, b);
    let db = det(b);

    // Expand arg2: T(b0,ABr1,ABr2) ≡ a1x*T(b0,b0,R2) + a1y*T(b0,b1,R2) + a1z*T(b0,b2,R2)
    lemma_triple_expand_arg2_3(b0, a1.x, b0, a1.y, b1, a1.z, b2, ab.row2);

    // Kill first (self_zero_12)
    crate::vec3::ops::lemma_triple_self_zero_12(b0, ab.row2);
    lemma_mul_zero_by_eqv(a1.x, triple(b0, b0, ab.row2));
    let (e0, e1, e2) = (
        a1.x.mul(triple(b0, b0, ab.row2)),
        a1.y.mul(triple(b0, b1, ab.row2)),
        a1.z.mul(triple(b0, b2, ab.row2)),
    );
    lemma_sum3_kill_first(e0, e1, e2);
    T::axiom_eqv_transitive(triple(b0, ab.row1, ab.row2), e0.add(e1).add(e2), e1.add(e2));

    // Expand T(b0,b1,ABr2) in arg3, kill first two
    lemma_triple_expand_arg3_3(b0, b1, a2.x, b0, a2.y, b1, a2.z, b2);
    crate::vec3::ops::lemma_triple_self_zero_13(b0, b1);
    crate::vec3::ops::lemma_triple_self_zero_23(b0, b1);
    lemma_mul_zero_by_eqv(a2.x, triple(b0, b1, b0));
    lemma_mul_zero_by_eqv(a2.y, triple(b0, b1, b1));
    lemma_sum3_kill_first_second(
        a2.x.mul(triple(b0, b1, b0)), a2.y.mul(triple(b0, b1, b1)),
        a2.z.mul(triple(b0, b1, b2)));
    // T(b0,b1,ABr2) ≡ a2z*db  (since T(b0,b1,b2) = db definitionally)
    T::axiom_eqv_transitive(triple(b0, b1, ab.row2),
        a2.x.mul(triple(b0, b1, b0)).add(a2.y.mul(triple(b0, b1, b1))).add(a2.z.mul(db)),
        a2.z.mul(db));
    // e1 = a1y*T(b0,b1,ABr2) ≡ a1y*(a2z*db) ≡ (a1y*a2z)*db
    ring_lemmas::lemma_mul_congruence_right(a1.y, triple(b0, b1, ab.row2), a2.z.mul(db));
    T::axiom_mul_associative(a1.y, a2.z, db);
    T::axiom_eqv_symmetric(a1.y.mul(a2.z).mul(db), a1.y.mul(a2.z.mul(db)));
    T::axiom_eqv_transitive(e1, a1.y.mul(a2.z.mul(db)), a1.y.mul(a2.z).mul(db));

    // Expand T(b0,b2,ABr2) in arg3, kill first and third
    lemma_triple_expand_arg3_3(b0, b2, a2.x, b0, a2.y, b1, a2.z, b2);
    crate::vec3::ops::lemma_triple_self_zero_13(b0, b2);
    crate::vec3::ops::lemma_triple_self_zero_23(b0, b2);
    lemma_mul_zero_by_eqv(a2.x, triple(b0, b2, b0));
    lemma_mul_zero_by_eqv(a2.z, triple(b0, b2, b2));
    lemma_sum3_kill_first_third(
        a2.x.mul(triple(b0, b2, b0)), a2.y.mul(triple(b0, b2, b1)),
        a2.z.mul(triple(b0, b2, b2)));
    // T(b0,b2,ABr2) ≡ a2y*T(b0,b2,b1)
    T::axiom_eqv_transitive(triple(b0, b2, ab.row2),
        a2.x.mul(triple(b0, b2, b0)).add(a2.y.mul(triple(b0, b2, b1))).add(a2.z.mul(triple(b0, b2, b2))),
        a2.y.mul(triple(b0, b2, b1)));

    // T(b0,b2,b1) ≡ -db by swap_23
    crate::vec3::ops::lemma_triple_swap_23(b0, b1, b2);
    // a2y*T(b0,b2,b1) ≡ a2y*(-db) ≡ -(a2y*db)
    ring_lemmas::lemma_mul_congruence_right(a2.y, triple(b0, b2, b1), db.neg());
    ring_lemmas::lemma_mul_neg_right(a2.y, db);
    T::axiom_eqv_transitive(a2.y.mul(triple(b0, b2, b1)), a2.y.mul(db.neg()), a2.y.mul(db).neg());
    // T(b0,b2,ABr2) ≡ -(a2y*db)
    T::axiom_eqv_transitive(triple(b0, b2, ab.row2), a2.y.mul(triple(b0, b2, b1)), a2.y.mul(db).neg());

    // e2 = a1z*T(b0,b2,ABr2) ≡ a1z*(-(a2y*db)) ≡ -((a1z*a2y)*db)
    ring_lemmas::lemma_mul_congruence_right(a1.z, triple(b0, b2, ab.row2), a2.y.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a1.z, a2.y.mul(db));
    T::axiom_eqv_transitive(e2, a1.z.mul(a2.y.mul(db).neg()), a1.z.mul(a2.y.mul(db)).neg());
    T::axiom_mul_associative(a1.z, a2.y, db);
    T::axiom_eqv_symmetric(a1.z.mul(a2.y).mul(db), a1.z.mul(a2.y.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a1.z.mul(a2.y.mul(db)), a1.z.mul(a2.y).mul(db));
    T::axiom_eqv_transitive(e2, a1.z.mul(a2.y.mul(db)).neg(), a1.z.mul(a2.y).mul(db).neg());

    // Combine: e1 + e2 ≡ (a1y*a2z)*db + -((a1z*a2y)*db)
    T::axiom_add_congruence_left(e1, a1.y.mul(a2.z).mul(db), e2);
    additive_group_lemmas::lemma_add_congruence_right(
        a1.y.mul(a2.z).mul(db), e2, a1.z.mul(a2.y).mul(db).neg());
    T::axiom_eqv_transitive(e1.add(e2),
        a1.y.mul(a2.z).mul(db).add(e2),
        a1.y.mul(a2.z).mul(db).add(a1.z.mul(a2.y).mul(db).neg()));

    // Factor: p*db + (-(q*db)) ≡ (p-q)*db
    let p = a1.y.mul(a2.z);
    let q = a1.z.mul(a2.y);
    T::axiom_sub_is_add_neg(p.mul(db), q.mul(db));
    T::axiom_eqv_symmetric(p.mul(db).sub(q.mul(db)), p.mul(db).add(q.mul(db).neg()));
    ring_lemmas::lemma_sub_mul_right(p, q, db);
    T::axiom_eqv_symmetric(p.sub(q).mul(db), p.mul(db).sub(q.mul(db)));
    T::axiom_eqv_transitive(
        p.mul(db).add(q.mul(db).neg()),
        p.mul(db).sub(q.mul(db)),
        p.sub(q).mul(db));
    T::axiom_eqv_transitive(e1.add(e2),
        p.mul(db).add(q.mul(db).neg()),
        cross(a1, a2).x.mul(db));

    // Final chain
    T::axiom_eqv_transitive(triple(b0, ab.row1, ab.row2), e1.add(e2), cross(a1, a2).x.mul(db));
}

/// Column 1 of det multiplicative: triple(b1, ABr1, ABr2) ≡ cross(a1,a2).y * det(b)
proof fn lemma_det_mul_col1<T: Ring>(a: Mat3x3<T>, b: Mat3x3<T>)
    ensures triple(b.row1, mat_mul(a,b).row1, mat_mul(a,b).row2)
            .eqv(cross(a.row1, a.row2).y.mul(det(b))),
{
    let a1 = a.row1; let a2 = a.row2;
    let (b0, b1, b2) = (b.row0, b.row1, b.row2);
    let ab = mat_mul(a, b);
    let db = det(b);

    // Expand arg2: T(b1,ABr1,ABr2) ≡ a1x*T(b1,b0,R2) + a1y*T(b1,b1,R2) + a1z*T(b1,b2,R2)
    lemma_triple_expand_arg2_3(b1, a1.x, b0, a1.y, b1, a1.z, b2, ab.row2);

    // Kill second (self_zero_12 on b1,b1)
    crate::vec3::ops::lemma_triple_self_zero_12(b1, ab.row2);
    lemma_mul_zero_by_eqv(a1.y, triple(b1, b1, ab.row2));
    let (e0, e1, e2) = (
        a1.x.mul(triple(b1, b0, ab.row2)),
        a1.y.mul(triple(b1, b1, ab.row2)),
        a1.z.mul(triple(b1, b2, ab.row2)),
    );
    lemma_sum3_kill_second(e0, e1, e2);
    T::axiom_eqv_transitive(triple(b1, ab.row1, ab.row2), e0.add(e1).add(e2), e0.add(e2));

    // Expand T(b1,b0,ABr2) in arg3, kill first two
    // T(b1,b0,b0)≡0 [sz23], T(b1,b0,b1)≡0 [sz13], survivor: a2z*T(b1,b0,b2)
    lemma_triple_expand_arg3_3(b1, b0, a2.x, b0, a2.y, b1, a2.z, b2);
    crate::vec3::ops::lemma_triple_self_zero_23(b1, b0);
    crate::vec3::ops::lemma_triple_self_zero_13(b1, b0);
    lemma_mul_zero_by_eqv(a2.x, triple(b1, b0, b0));
    lemma_mul_zero_by_eqv(a2.y, triple(b1, b0, b1));
    lemma_sum3_kill_first_second(
        a2.x.mul(triple(b1, b0, b0)), a2.y.mul(triple(b1, b0, b1)),
        a2.z.mul(triple(b1, b0, b2)));
    T::axiom_eqv_transitive(triple(b1, b0, ab.row2),
        a2.x.mul(triple(b1, b0, b0)).add(a2.y.mul(triple(b1, b0, b1))).add(a2.z.mul(triple(b1, b0, b2))),
        a2.z.mul(triple(b1, b0, b2)));

    // T(b1,b0,b2) ≡ -db by swap_12
    crate::vec3::ops::lemma_triple_swap_12(b0, b1, b2);
    // swap_12 gives triple(b0,b1,b2) ≡ triple(b1,b0,b2).neg()
    // → triple(b1,b0,b2) ≡ -(-db)... wait, need the right direction
    // swap_12(a,b,c): triple(a,b,c) ≡ triple(b,a,c).neg()
    // So swap_12(b0,b1,b2): triple(b0,b1,b2) ≡ triple(b1,b0,b2).neg()
    // → triple(b1,b0,b2).neg() ≡ db by symmetric
    // → triple(b1,b0,b2) ≡ -db by neg_involution reasoning
    T::axiom_eqv_symmetric(triple(b0, b1, b2), triple(b1, b0, b2).neg());
    // db ≡ triple(b1,b0,b2).neg()
    additive_group_lemmas::lemma_neg_congruence(db, triple(b1, b0, b2).neg());
    // db.neg() ≡ triple(b1,b0,b2).neg().neg()
    additive_group_lemmas::lemma_neg_involution(triple(b1, b0, b2));
    // triple(b1,b0,b2).neg().neg() ≡ triple(b1,b0,b2)
    T::axiom_eqv_symmetric(triple(b1, b0, b2).neg().neg(), triple(b1, b0, b2));
    // triple(b1,b0,b2) ≡ triple(b1,b0,b2).neg().neg() ≡ db.neg()
    T::axiom_eqv_transitive(db.neg(), triple(b1, b0, b2).neg().neg(), triple(b1, b0, b2));
    T::axiom_eqv_symmetric(db.neg(), triple(b1, b0, b2));
    // triple(b1,b0,b2) ≡ db.neg()

    // T(b1,b0,ABr2) ≡ a2z*T(b1,b0,b2) ≡ a2z*(-db) ≡ -(a2z*db)
    ring_lemmas::lemma_mul_congruence_right(a2.z, triple(b1, b0, b2), db.neg());
    ring_lemmas::lemma_mul_neg_right(a2.z, db);
    T::axiom_eqv_transitive(a2.z.mul(triple(b1, b0, b2)), a2.z.mul(db.neg()), a2.z.mul(db).neg());
    T::axiom_eqv_transitive(triple(b1, b0, ab.row2), a2.z.mul(triple(b1, b0, b2)), a2.z.mul(db).neg());

    // e0 = a1x*T(b1,b0,ABr2) ≡ a1x*(-(a2z*db)) ≡ -((a1x*a2z)*db)
    ring_lemmas::lemma_mul_congruence_right(a1.x, triple(b1, b0, ab.row2), a2.z.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a1.x, a2.z.mul(db));
    T::axiom_eqv_transitive(e0, a1.x.mul(a2.z.mul(db).neg()), a1.x.mul(a2.z.mul(db)).neg());
    T::axiom_mul_associative(a1.x, a2.z, db);
    T::axiom_eqv_symmetric(a1.x.mul(a2.z).mul(db), a1.x.mul(a2.z.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a1.x.mul(a2.z.mul(db)), a1.x.mul(a2.z).mul(db));
    T::axiom_eqv_transitive(e0, a1.x.mul(a2.z.mul(db)).neg(), a1.x.mul(a2.z).mul(db).neg());

    // Expand T(b1,b2,ABr2) in arg3, kill second and third
    // T(b1,b2,b1)≡0 [sz13], T(b1,b2,b2)≡0 [sz23], survivor: a2x*T(b1,b2,b0)
    lemma_triple_expand_arg3_3(b1, b2, a2.x, b0, a2.y, b1, a2.z, b2);
    crate::vec3::ops::lemma_triple_self_zero_13(b1, b2);
    crate::vec3::ops::lemma_triple_self_zero_23(b1, b2);
    lemma_mul_zero_by_eqv(a2.y, triple(b1, b2, b1));
    lemma_mul_zero_by_eqv(a2.z, triple(b1, b2, b2));
    lemma_sum3_kill_second_third(
        a2.x.mul(triple(b1, b2, b0)), a2.y.mul(triple(b1, b2, b1)),
        a2.z.mul(triple(b1, b2, b2)));
    T::axiom_eqv_transitive(triple(b1, b2, ab.row2),
        a2.x.mul(triple(b1, b2, b0)).add(a2.y.mul(triple(b1, b2, b1))).add(a2.z.mul(triple(b1, b2, b2))),
        a2.x.mul(triple(b1, b2, b0)));

    // T(b1,b2,b0) ≡ db by cyclic: triple(b0,b1,b2) ≡ triple(b1,b2,b0)
    crate::vec3::ops::lemma_triple_cyclic(b0, b1, b2);
    T::axiom_eqv_symmetric(triple(b0, b1, b2), triple(b1, b2, b0));
    // triple(b1,b2,b0) ≡ db

    // T(b1,b2,ABr2) ≡ a2x*db
    ring_lemmas::lemma_mul_congruence_right(a2.x, triple(b1, b2, b0), db);
    T::axiom_eqv_transitive(triple(b1, b2, ab.row2), a2.x.mul(triple(b1, b2, b0)), a2.x.mul(db));

    // e2 = a1z*T(b1,b2,ABr2) ≡ a1z*(a2x*db) ≡ (a1z*a2x)*db
    ring_lemmas::lemma_mul_congruence_right(a1.z, triple(b1, b2, ab.row2), a2.x.mul(db));
    T::axiom_mul_associative(a1.z, a2.x, db);
    T::axiom_eqv_symmetric(a1.z.mul(a2.x).mul(db), a1.z.mul(a2.x.mul(db)));
    T::axiom_eqv_transitive(e2, a1.z.mul(a2.x.mul(db)), a1.z.mul(a2.x).mul(db));

    // Combine: e0 + e2 ≡ -((a1x*a2z)*db) + (a1z*a2x)*db
    // Need to commute: -(X) + Y = Y + (-(X)) = Y - X = (a1z*a2x - a1x*a2z)*db = cross(a1,a2).y*db
    T::axiom_add_congruence_left(e0, a1.x.mul(a2.z).mul(db).neg(), e2);
    additive_group_lemmas::lemma_add_congruence_right(
        a1.x.mul(a2.z).mul(db).neg(), e2, a1.z.mul(a2.x).mul(db));
    T::axiom_eqv_transitive(e0.add(e2),
        a1.x.mul(a2.z).mul(db).neg().add(e2),
        a1.x.mul(a2.z).mul(db).neg().add(a1.z.mul(a2.x).mul(db)));

    // Commute: -(q*db) + (p*db) ≡ (p*db) + (-(q*db)) = p*db - q*db
    let p = a1.z.mul(a2.x);
    let q = a1.x.mul(a2.z);
    T::axiom_add_commutative(q.mul(db).neg(), p.mul(db));
    T::axiom_eqv_transitive(e0.add(e2),
        q.mul(db).neg().add(p.mul(db)),
        p.mul(db).add(q.mul(db).neg()));

    // Factor: p*db + (-(q*db)) ≡ (p-q)*db
    T::axiom_sub_is_add_neg(p.mul(db), q.mul(db));
    T::axiom_eqv_symmetric(p.mul(db).sub(q.mul(db)), p.mul(db).add(q.mul(db).neg()));
    ring_lemmas::lemma_sub_mul_right(p, q, db);
    T::axiom_eqv_symmetric(p.sub(q).mul(db), p.mul(db).sub(q.mul(db)));
    T::axiom_eqv_transitive(
        p.mul(db).add(q.mul(db).neg()),
        p.mul(db).sub(q.mul(db)),
        p.sub(q).mul(db));
    T::axiom_eqv_transitive(e0.add(e2),
        p.mul(db).add(q.mul(db).neg()),
        cross(a1, a2).y.mul(db));

    // Final chain
    T::axiom_eqv_transitive(triple(b1, ab.row1, ab.row2), e0.add(e2), cross(a1, a2).y.mul(db));
}

/// Column 2 of det multiplicative: triple(b2, ABr1, ABr2) ≡ cross(a1,a2).z * det(b)
proof fn lemma_det_mul_col2<T: Ring>(a: Mat3x3<T>, b: Mat3x3<T>)
    ensures triple(b.row2, mat_mul(a,b).row1, mat_mul(a,b).row2)
            .eqv(cross(a.row1, a.row2).z.mul(det(b))),
{
    let a1 = a.row1; let a2 = a.row2;
    let (b0, b1, b2) = (b.row0, b.row1, b.row2);
    let ab = mat_mul(a, b);
    let db = det(b);

    // Expand arg2: T(b2,ABr1,ABr2) ≡ a1x*T(b2,b0,R2) + a1y*T(b2,b1,R2) + a1z*T(b2,b2,R2)
    lemma_triple_expand_arg2_3(b2, a1.x, b0, a1.y, b1, a1.z, b2, ab.row2);

    // Kill third (self_zero_12 on b2,b2)
    crate::vec3::ops::lemma_triple_self_zero_12(b2, ab.row2);
    lemma_mul_zero_by_eqv(a1.z, triple(b2, b2, ab.row2));
    let (e0, e1, e2) = (
        a1.x.mul(triple(b2, b0, ab.row2)),
        a1.y.mul(triple(b2, b1, ab.row2)),
        a1.z.mul(triple(b2, b2, ab.row2)),
    );
    lemma_sum3_kill_third(e0, e1, e2);
    T::axiom_eqv_transitive(triple(b2, ab.row1, ab.row2), e0.add(e1).add(e2), e0.add(e1));

    // Expand T(b2,b0,ABr2) in arg3
    // T(b2,b0,b0)≡0 [sz23], T(b2,b0,b2)≡0 [sz13], survivor: a2y*T(b2,b0,b1)
    lemma_triple_expand_arg3_3(b2, b0, a2.x, b0, a2.y, b1, a2.z, b2);
    crate::vec3::ops::lemma_triple_self_zero_23(b2, b0);
    crate::vec3::ops::lemma_triple_self_zero_13(b2, b0);
    lemma_mul_zero_by_eqv(a2.x, triple(b2, b0, b0));
    lemma_mul_zero_by_eqv(a2.z, triple(b2, b0, b2));
    lemma_sum3_kill_first_third(
        a2.x.mul(triple(b2, b0, b0)), a2.y.mul(triple(b2, b0, b1)),
        a2.z.mul(triple(b2, b0, b2)));
    T::axiom_eqv_transitive(triple(b2, b0, ab.row2),
        a2.x.mul(triple(b2, b0, b0)).add(a2.y.mul(triple(b2, b0, b1))).add(a2.z.mul(triple(b2, b0, b2))),
        a2.y.mul(triple(b2, b0, b1)));

    // T(b2,b0,b1) ≡ db by double cyclic
    crate::vec3::ops::lemma_triple_cyclic(b0, b1, b2);
    crate::vec3::ops::lemma_triple_cyclic(b1, b2, b0);
    // T(b0,b1,b2) ≡ T(b1,b2,b0) ≡ T(b2,b0,b1)
    T::axiom_eqv_transitive(triple(b0, b1, b2), triple(b1, b2, b0), triple(b2, b0, b1));
    T::axiom_eqv_symmetric(db, triple(b2, b0, b1));
    // triple(b2,b0,b1) ≡ db

    // T(b2,b0,ABr2) ≡ a2y*db
    ring_lemmas::lemma_mul_congruence_right(a2.y, triple(b2, b0, b1), db);
    T::axiom_eqv_transitive(triple(b2, b0, ab.row2), a2.y.mul(triple(b2, b0, b1)), a2.y.mul(db));

    // e0 = a1x*T(b2,b0,ABr2) ≡ a1x*(a2y*db) ≡ (a1x*a2y)*db
    ring_lemmas::lemma_mul_congruence_right(a1.x, triple(b2, b0, ab.row2), a2.y.mul(db));
    T::axiom_mul_associative(a1.x, a2.y, db);
    T::axiom_eqv_symmetric(a1.x.mul(a2.y).mul(db), a1.x.mul(a2.y.mul(db)));
    T::axiom_eqv_transitive(e0, a1.x.mul(a2.y.mul(db)), a1.x.mul(a2.y).mul(db));

    // Expand T(b2,b1,ABr2) in arg3
    // T(b2,b1,b1)≡0 [sz23], T(b2,b1,b2)≡0 [sz13], survivor: a2x*T(b2,b1,b0)
    lemma_triple_expand_arg3_3(b2, b1, a2.x, b0, a2.y, b1, a2.z, b2);
    crate::vec3::ops::lemma_triple_self_zero_23(b2, b1);
    crate::vec3::ops::lemma_triple_self_zero_13(b2, b1);
    lemma_mul_zero_by_eqv(a2.y, triple(b2, b1, b1));
    lemma_mul_zero_by_eqv(a2.z, triple(b2, b1, b2));
    lemma_sum3_kill_second_third(
        a2.x.mul(triple(b2, b1, b0)), a2.y.mul(triple(b2, b1, b1)),
        a2.z.mul(triple(b2, b1, b2)));
    T::axiom_eqv_transitive(triple(b2, b1, ab.row2),
        a2.x.mul(triple(b2, b1, b0)).add(a2.y.mul(triple(b2, b1, b1))).add(a2.z.mul(triple(b2, b1, b2))),
        a2.x.mul(triple(b2, b1, b0)));

    // T(b2,b1,b0) ≡ -db
    // swap_12(b1,b2,b0): triple(b1,b2,b0) ≡ triple(b2,b1,b0).neg()
    crate::vec3::ops::lemma_triple_swap_12(b1, b2, b0);
    // triple(b1,b2,b0) ≡ db by cyclic
    crate::vec3::ops::lemma_triple_cyclic(b0, b1, b2);
    T::axiom_eqv_symmetric(db, triple(b1, b2, b0));
    // triple(b1,b2,b0) ≡ db, and triple(b1,b2,b0) ≡ triple(b2,b1,b0).neg()
    // → db ≡ triple(b2,b1,b0).neg()
    T::axiom_eqv_symmetric(triple(b1, b2, b0), triple(b2, b1, b0).neg());
    T::axiom_eqv_transitive(db, triple(b1, b2, b0), triple(b2, b1, b0).neg());
    // → triple(b2,b1,b0) ≡ -db
    additive_group_lemmas::lemma_neg_congruence(db, triple(b2, b1, b0).neg());
    additive_group_lemmas::lemma_neg_involution(triple(b2, b1, b0));
    T::axiom_eqv_symmetric(triple(b2, b1, b0).neg().neg(), triple(b2, b1, b0));
    T::axiom_eqv_transitive(db.neg(), triple(b2, b1, b0).neg().neg(), triple(b2, b1, b0));
    T::axiom_eqv_symmetric(db.neg(), triple(b2, b1, b0));

    // a2x*T(b2,b1,b0) ≡ a2x*(-db) ≡ -(a2x*db)
    ring_lemmas::lemma_mul_congruence_right(a2.x, triple(b2, b1, b0), db.neg());
    ring_lemmas::lemma_mul_neg_right(a2.x, db);
    T::axiom_eqv_transitive(a2.x.mul(triple(b2, b1, b0)), a2.x.mul(db.neg()), a2.x.mul(db).neg());
    T::axiom_eqv_transitive(triple(b2, b1, ab.row2), a2.x.mul(triple(b2, b1, b0)), a2.x.mul(db).neg());

    // e1 = a1y*T(b2,b1,ABr2) ≡ a1y*(-(a2x*db)) ≡ -((a1y*a2x)*db)
    ring_lemmas::lemma_mul_congruence_right(a1.y, triple(b2, b1, ab.row2), a2.x.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a1.y, a2.x.mul(db));
    T::axiom_eqv_transitive(e1, a1.y.mul(a2.x.mul(db).neg()), a1.y.mul(a2.x.mul(db)).neg());
    T::axiom_mul_associative(a1.y, a2.x, db);
    T::axiom_eqv_symmetric(a1.y.mul(a2.x).mul(db), a1.y.mul(a2.x.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a1.y.mul(a2.x.mul(db)), a1.y.mul(a2.x).mul(db));
    T::axiom_eqv_transitive(e1, a1.y.mul(a2.x.mul(db)).neg(), a1.y.mul(a2.x).mul(db).neg());

    // Combine: e0 + e1 ≡ (a1x*a2y)*db + -((a1y*a2x)*db)
    T::axiom_add_congruence_left(e0, a1.x.mul(a2.y).mul(db), e1);
    additive_group_lemmas::lemma_add_congruence_right(
        a1.x.mul(a2.y).mul(db), e1, a1.y.mul(a2.x).mul(db).neg());
    T::axiom_eqv_transitive(e0.add(e1),
        a1.x.mul(a2.y).mul(db).add(e1),
        a1.x.mul(a2.y).mul(db).add(a1.y.mul(a2.x).mul(db).neg()));

    // Factor: p*db + (-(q*db)) ≡ (p-q)*db = cross(a1,a2).z * db
    let p = a1.x.mul(a2.y);
    let q = a1.y.mul(a2.x);
    T::axiom_sub_is_add_neg(p.mul(db), q.mul(db));
    T::axiom_eqv_symmetric(p.mul(db).sub(q.mul(db)), p.mul(db).add(q.mul(db).neg()));
    ring_lemmas::lemma_sub_mul_right(p, q, db);
    T::axiom_eqv_symmetric(p.sub(q).mul(db), p.mul(db).sub(q.mul(db)));
    T::axiom_eqv_transitive(
        p.mul(db).add(q.mul(db).neg()),
        p.mul(db).sub(q.mul(db)),
        p.sub(q).mul(db));
    T::axiom_eqv_transitive(e0.add(e1),
        p.mul(db).add(q.mul(db).neg()),
        cross(a1, a2).z.mul(db));

    // Final chain
    T::axiom_eqv_transitive(triple(b2, ab.row1, ab.row2), e0.add(e1), cross(a1, a2).z.mul(db));
}

/// det(mat_mul(a, b)) ≡ det(a) * det(b)
pub proof fn lemma_det_multiplicative<T: Ring>(a: Mat3x3<T>, b: Mat3x3<T>)
    ensures det(mat_mul(a, b)).eqv(det(a).mul(det(b))),
{
    let a0 = a.row0; let a1 = a.row1; let a2 = a.row2;
    let (b0, b1, b2) = (b.row0, b.row1, b.row2);
    let ab = mat_mul(a, b);
    let db = det(b);
    let c = cross(a1, a2);

    // Phase 1: det(AB) = triple(ABr0, ABr1, ABr2)
    // ABr0 = scale(a0x,b0) + scale(a0y,b1) + scale(a0z,b2)
    // → ≡ a0x*T(b0,ABr1,ABr2) + a0y*T(b1,ABr1,ABr2) + a0z*T(b2,ABr1,ABr2)
    lemma_triple_expand_arg1_3(a0.x, b0, a0.y, b1, a0.z, b2, ab.row1, ab.row2);

    // Phase 2-4: Per-column results
    lemma_det_mul_col0(a, b); // T(b0,ABr1,ABr2) ≡ c.x * db
    lemma_det_mul_col1(a, b); // T(b1,ABr1,ABr2) ≡ c.y * db
    lemma_det_mul_col2(a, b); // T(b2,ABr1,ABr2) ≡ c.z * db

    // a0x * T0 ≡ a0x * (c.x * db) by mul_congruence_right
    ring_lemmas::lemma_mul_congruence_right(a0.x, triple(b0, ab.row1, ab.row2), c.x.mul(db));
    ring_lemmas::lemma_mul_congruence_right(a0.y, triple(b1, ab.row1, ab.row2), c.y.mul(db));
    ring_lemmas::lemma_mul_congruence_right(a0.z, triple(b2, ab.row1, ab.row2), c.z.mul(db));

    // a0i * (c.i * db) ≡ (a0i * c.i) * db by mul_associative
    T::axiom_mul_associative(a0.x, c.x, db);
    T::axiom_eqv_symmetric(a0.x.mul(c.x).mul(db), a0.x.mul(c.x.mul(db)));
    T::axiom_eqv_transitive(a0.x.mul(triple(b0, ab.row1, ab.row2)), a0.x.mul(c.x.mul(db)), a0.x.mul(c.x).mul(db));
    T::axiom_mul_associative(a0.y, c.y, db);
    T::axiom_eqv_symmetric(a0.y.mul(c.y).mul(db), a0.y.mul(c.y.mul(db)));
    T::axiom_eqv_transitive(a0.y.mul(triple(b1, ab.row1, ab.row2)), a0.y.mul(c.y.mul(db)), a0.y.mul(c.y).mul(db));
    T::axiom_mul_associative(a0.z, c.z, db);
    T::axiom_eqv_symmetric(a0.z.mul(c.z).mul(db), a0.z.mul(c.z.mul(db)));
    T::axiom_eqv_transitive(a0.z.mul(triple(b2, ab.row1, ab.row2)), a0.z.mul(c.z.mul(db)), a0.z.mul(c.z).mul(db));

    // 3-sum congruence: a0x*T0 + a0y*T1 + a0z*T2 ≡ (a0x*cx)*db + (a0y*cy)*db + (a0z*cz)*db
    lemma_add_congruence_3(
        a0.x.mul(triple(b0, ab.row1, ab.row2)), a0.x.mul(c.x).mul(db),
        a0.y.mul(triple(b1, ab.row1, ab.row2)), a0.y.mul(c.y).mul(db),
        a0.z.mul(triple(b2, ab.row1, ab.row2)), a0.z.mul(c.z).mul(db));

    // Phase 5: Factor out db
    // (a0x*cx)*db + (a0y*cy)*db + (a0z*cz)*db ≡ (a0x*cx + a0y*cy + a0z*cz)*db
    lemma_factor_3(a0.x.mul(c.x), a0.y.mul(c.y), a0.z.mul(c.z), db);
    // (a0x*cx + a0y*cy + a0z*cz) = dot(a0, c) = dot(a0, cross(a1,a2)) = det(a) definitionally

    // Chain: det(AB) ≡ 3-sum of T_j ≡ 3-sum of (a0i*ci)*db ≡ dot(a0,c)*db = det(a)*det(b)
    let sum_orig = a0.x.mul(triple(b0, ab.row1, ab.row2))
        .add(a0.y.mul(triple(b1, ab.row1, ab.row2)))
        .add(a0.z.mul(triple(b2, ab.row1, ab.row2)));
    let sum_factored = a0.x.mul(c.x).mul(db)
        .add(a0.y.mul(c.y).mul(db))
        .add(a0.z.mul(c.z).mul(db));

    T::axiom_eqv_transitive(det(ab), sum_orig, sum_factored);
    T::axiom_eqv_transitive(det(ab), sum_factored, det(a).mul(db));
}

// ---------------------------------------------------------------------------
// Det inverse and inverse involution
// ---------------------------------------------------------------------------

/// det(inverse(m)) ≡ recip(det(m)) when det(m) ≢ 0
pub proof fn lemma_det_inverse<T: Field>(m: Mat3x3<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        det(inverse(m)).eqv(det(m).recip()),
{
    let d = det(m);
    let inv = inverse(m);

    // m * inv ≡ I (row-wise)
    lemma_inverse_right(m);

    // det(m * inv) ≡ det(I) via det_congruence
    lemma_det_congruence(mat_mul(m, inv), identity::<T>());

    // det(I) ≡ 1
    lemma_det_identity::<T>();

    // det(m * inv) ≡ 1
    T::axiom_eqv_transitive(det(mat_mul(m, inv)), det(identity::<T>()), T::one());

    // det(m * inv) ≡ det(m) * det(inv) by det_multiplicative
    lemma_det_multiplicative(m, inv);
    T::axiom_eqv_symmetric(det(mat_mul(m, inv)), d.mul(det(inv)));

    // d * det(inv) ≡ 1
    T::axiom_eqv_transitive(d.mul(det(inv)), det(mat_mul(m, inv)), T::one());

    // By recip_unique, det(inv) ≡ recip(d)
    field_lemmas::lemma_recip_unique::<T>(d, det(inv));
}

/// Helper: recip(d) ≢ 0 when d ≢ 0
proof fn lemma_recip_nonzero<T: Field>(d: T)
    requires !d.eqv(T::zero()),
    ensures !d.recip().eqv(T::zero()),
{
    if d.recip().eqv(T::zero()) {
        ring_lemmas::lemma_mul_congruence_right::<T>(d, d.recip(), T::zero());
        T::axiom_mul_zero_right(d);
        T::axiom_mul_recip_right(d);
        T::axiom_eqv_transitive(d.mul(d.recip()), d.mul(T::zero()), T::zero());
        T::axiom_eqv_symmetric(d.mul(d.recip()), T::one());
        T::axiom_eqv_transitive(T::one(), d.mul(d.recip()), T::zero());
        T::axiom_one_ne_zero();
    }
}

/// Helper: det(inverse(m)) ≢ 0 when det(m) ≢ 0
proof fn lemma_det_inv_nonzero<T: Field>(m: Mat3x3<T>)
    requires !det(m).eqv(T::zero()),
    ensures !det(inverse(m)).eqv(T::zero()),
{
    lemma_det_inverse(m);
    lemma_recip_nonzero::<T>(det(m));
    // det(inv) ≡ recip(d) and recip(d) ≢ 0
    // If det(inv) ≡ 0 then recip(d) ≡ det(inv) ≡ 0, contradiction
    if det(inverse(m)).eqv(T::zero()) {
        T::axiom_eqv_symmetric(det(inverse(m)), det(m).recip());
        T::axiom_eqv_transitive(det(m).recip(), det(inverse(m)), T::zero());
    }
}

/// Helper: mat_vec_mul(inv(m), mat_vec_mul(m, v)) ≡ v
proof fn lemma_inv_m_cancel_left<T: Field>(m: Mat3x3<T>, v: Vec3<T>)
    requires !det(m).eqv(T::zero()),
    ensures mat_vec_mul(inverse(m), mat_vec_mul(m, v)).eqv(v),
{
    let inv = inverse(m);
    // inv*m = I row-wise
    lemma_inverse_left(m);
    // mat_vec_mul(inv, mat_vec_mul(m, v)) ≡ mat_vec_mul(inv*m, v)
    lemma_mat_vec_mul_mat_mul(inv, m, v);
    // mat_vec_mul(inv*m, v) ≡ mat_vec_mul(I, v) by dot_congruence
    Vec3::<T>::axiom_eqv_reflexive(v);
    crate::vec3::ops::lemma_dot_congruence(
        mat_mul(inv, m).row0, identity::<T>().row0, v, v);
    crate::vec3::ops::lemma_dot_congruence(
        mat_mul(inv, m).row1, identity::<T>().row1, v, v);
    crate::vec3::ops::lemma_dot_congruence(
        mat_mul(inv, m).row2, identity::<T>().row2, v, v);
    // mat_vec_mul(I, v) ≡ v
    lemma_identity_mul_vec(v);
    // Chain each component
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, v)).x,
        mat_vec_mul(mat_mul(inv, m), v).x,
        mat_vec_mul(identity(), v).x);
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, v)).x,
        mat_vec_mul(identity(), v).x, v.x);
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, v)).y,
        mat_vec_mul(mat_mul(inv, m), v).y,
        mat_vec_mul(identity(), v).y);
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, v)).y,
        mat_vec_mul(identity(), v).y, v.y);
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, v)).z,
        mat_vec_mul(mat_mul(inv, m), v).z,
        mat_vec_mul(identity(), v).z);
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, v)).z,
        mat_vec_mul(identity(), v).z, v.z);
}

/// inverse(inverse(m)) ≡ m when det(m) ≢ 0
pub proof fn lemma_inverse_involution<T: Field>(m: Mat3x3<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        inverse(inverse(m)).row0.eqv(m.row0),
        inverse(inverse(m)).row1.eqv(m.row1),
        inverse(inverse(m)).row2.eqv(m.row2),
{
    let inv = inverse(m);
    let inv2 = inverse(inv);

    // det(inv) ≢ 0
    lemma_det_inv_nonzero(m);

    // For each basis vector e_j, mat_vec_mul(m, v) ≡ solve(inv, v):
    // Because mat_vec_mul(inv, mat_vec_mul(m, v)) ≡ v, solve_unique gives
    // mat_vec_mul(m, v) ≡ solve(inv, v) = mat_vec_mul(inv2, v)
    let e0 = Vec3::<T> { x: T::one(), y: T::zero(), z: T::zero() };
    let e1 = Vec3::<T> { x: T::zero(), y: T::one(), z: T::zero() };
    let e2 = Vec3::<T> { x: T::zero(), y: T::zero(), z: T::one() };

    // Show mat_vec_mul(inv, mat_vec_mul(m, e_j)) ≡ e_j
    lemma_inv_m_cancel_left(m, e0);
    lemma_inv_m_cancel_left(m, e1);
    lemma_inv_m_cancel_left(m, e2);

    // By solve_unique: mat_vec_mul(m, e_j) ≡ solve(inv, e_j) = mat_vec_mul(inv2, e_j)
    lemma_solve_unique(inv, mat_vec_mul(m, e0), e0);
    lemma_solve_unique(inv, mat_vec_mul(m, e1), e1);
    lemma_solve_unique(inv, mat_vec_mul(m, e2), e2);
    // mat_vec_mul(m, e_j) ≡ mat_vec_mul(inv2, e_j)

    // mat_vec_mul(M, e0) = (M.row0.x, M.row1.x, M.row2.x) = column 0 of M
    // So mat_vec_mul(m, e0).x = m.row0.x, mat_vec_mul(inv2, e0).x = inv2.row0.x
    // → m.row0.x ≡ inv2.row0.x (from column 0)
    // mat_vec_mul(m, e1).x = m.row0.y → m.row0.y ≡ inv2.row0.y (from column 1)
    // mat_vec_mul(m, e2).x = m.row0.z → m.row0.z ≡ inv2.row0.z (from column 2)

    // But wait, solve(inv, e0) = mat_vec_mul(inv2, e0). And the ensures of solve_unique
    // says mat_vec_mul(m, e0).eqv(solve(inv, e0)), which is component-wise equivalence.
    // solve(inv, e0) = mat_vec_mul(inv2, e0) definitionally.

    // Extract: mat_vec_mul(m, e0).x ≡ mat_vec_mul(inv2, e0).x
    // But mat_vec_mul(M, e0).x = dot(M.row0, e0).
    // dot(M.row0, e0) for any M:
    // We need dot(M.row0, e0) to equal M.row0.x. This is definitional since
    // e0 = (1, 0, 0) and dot(r, e0) = r.x*1 + r.y*0 + r.z*0 = r.x (modulo Ring ops).
    // But in the Ring setting, r.x*1+r.y*0+r.z*0 is NOT definitionally r.x!
    // We need lemma_dot_e0 which proves dot(r, e0) ≡ r.x.

    // Actually, mat_vec_mul(m, e_j) is defined as
    // Vec3 { x: dot(m.row0, e_j), y: dot(m.row1, e_j), z: dot(m.row2, e_j) }
    // And we have lemma_dot_e0(r): dot(r, e0) ≡ r.x, etc.

    // From the solve_unique ensures: mat_vec_mul(m, e0) .eqv. solve(inv, e0)
    // means mat_vec_mul(m, e0).x ≡ solve(inv, e0).x = mat_vec_mul(inv2, e0).x

    // dot(m.row0, e0) ≡ m.row0.x and dot(inv2.row0, e0) ≡ inv2.row0.x
    lemma_dot_e0_right(m.row0); lemma_dot_e0_right(m.row1); lemma_dot_e0_right(m.row2);
    lemma_dot_e0_right(inv2.row0); lemma_dot_e0_right(inv2.row1); lemma_dot_e0_right(inv2.row2);
    lemma_dot_e1_right(m.row0); lemma_dot_e1_right(m.row1); lemma_dot_e1_right(m.row2);
    lemma_dot_e1_right(inv2.row0); lemma_dot_e1_right(inv2.row1); lemma_dot_e1_right(inv2.row2);
    lemma_dot_e2_right(m.row0); lemma_dot_e2_right(m.row1); lemma_dot_e2_right(m.row2);
    lemma_dot_e2_right(inv2.row0); lemma_dot_e2_right(inv2.row1); lemma_dot_e2_right(inv2.row2);

    // Extract component equivalences from solve_unique results.
    // solve_unique gives: mat_vec_mul(m, ej).eqv(solve(inv, ej))
    // Since Vec3 eqv is open spec and component-wise, Z3 has:
    //   mat_vec_mul(m, ej).x ≡ solve(inv, ej).x  (= mat_vec_mul(inv2, ej).x)

    // Row 0, column 0: chain m.r0.x ≡ dot(m.r0,e0) ≡ dot(inv2.r0,e0) ≡ inv2.r0.x
    T::axiom_eqv_symmetric(dot(m.row0, e0), m.row0.x);
    T::axiom_eqv_transitive(m.row0.x, dot(m.row0, e0), dot(inv2.row0, e0));
    T::axiom_eqv_transitive(m.row0.x, dot(inv2.row0, e0), inv2.row0.x);
    T::axiom_eqv_symmetric(m.row0.x, inv2.row0.x);

    // From column 1: mat_vec_mul(m,e1).x ≡ solve(inv,e1).x
    T::axiom_eqv_symmetric(dot(m.row0, e1), m.row0.y);
    T::axiom_eqv_transitive(m.row0.y, dot(m.row0, e1), dot(inv2.row0, e1));
    T::axiom_eqv_transitive(m.row0.y, dot(inv2.row0, e1), inv2.row0.y);
    T::axiom_eqv_symmetric(m.row0.y, inv2.row0.y);

    // From column 2: mat_vec_mul(m,e2).x ≡ solve(inv,e2).x
    T::axiom_eqv_symmetric(dot(m.row0, e2), m.row0.z);
    T::axiom_eqv_transitive(m.row0.z, dot(m.row0, e2), dot(inv2.row0, e2));
    T::axiom_eqv_transitive(m.row0.z, dot(inv2.row0, e2), inv2.row0.z);
    T::axiom_eqv_symmetric(m.row0.z, inv2.row0.z);

    // Row 1
    T::axiom_eqv_symmetric(dot(m.row1, e0), m.row1.x);
    T::axiom_eqv_transitive(m.row1.x, dot(m.row1, e0), dot(inv2.row1, e0));
    T::axiom_eqv_transitive(m.row1.x, dot(inv2.row1, e0), inv2.row1.x);
    T::axiom_eqv_symmetric(m.row1.x, inv2.row1.x);

    T::axiom_eqv_symmetric(dot(m.row1, e1), m.row1.y);
    T::axiom_eqv_transitive(m.row1.y, dot(m.row1, e1), dot(inv2.row1, e1));
    T::axiom_eqv_transitive(m.row1.y, dot(inv2.row1, e1), inv2.row1.y);
    T::axiom_eqv_symmetric(m.row1.y, inv2.row1.y);

    T::axiom_eqv_symmetric(dot(m.row1, e2), m.row1.z);
    T::axiom_eqv_transitive(m.row1.z, dot(m.row1, e2), dot(inv2.row1, e2));
    T::axiom_eqv_transitive(m.row1.z, dot(inv2.row1, e2), inv2.row1.z);
    T::axiom_eqv_symmetric(m.row1.z, inv2.row1.z);

    // Row 2
    T::axiom_eqv_symmetric(dot(m.row2, e0), m.row2.x);
    T::axiom_eqv_transitive(m.row2.x, dot(m.row2, e0), dot(inv2.row2, e0));
    T::axiom_eqv_transitive(m.row2.x, dot(inv2.row2, e0), inv2.row2.x);
    T::axiom_eqv_symmetric(m.row2.x, inv2.row2.x);

    T::axiom_eqv_symmetric(dot(m.row2, e1), m.row2.y);
    T::axiom_eqv_transitive(m.row2.y, dot(m.row2, e1), dot(inv2.row2, e1));
    T::axiom_eqv_transitive(m.row2.y, dot(inv2.row2, e1), inv2.row2.y);
    T::axiom_eqv_symmetric(m.row2.y, inv2.row2.y);

    T::axiom_eqv_symmetric(dot(m.row2, e2), m.row2.z);
    T::axiom_eqv_transitive(m.row2.z, dot(m.row2, e2), dot(inv2.row2, e2));
    T::axiom_eqv_transitive(m.row2.z, dot(inv2.row2, e2), inv2.row2.z);
    T::axiom_eqv_symmetric(m.row2.z, inv2.row2.z);
}

// ---------------------------------------------------------------------------
// Linear system solving
// ---------------------------------------------------------------------------

/// Solve Ax = b for 3x3 systems: x = inverse(A) * b
pub open spec fn solve<T: Field>(m: Mat3x3<T>, b: Vec3<T>) -> Vec3<T> {
    mat_vec_mul(inverse(m), b)
}

/// Correctness: mat_vec_mul(m, solve(m, b)) ≡ b
pub proof fn lemma_solve_correct<T: Field>(m: Mat3x3<T>, b: Vec3<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        mat_vec_mul(m, solve(m, b)).eqv(b),
{
    let inv = inverse(m);

    lemma_mat_vec_mul_mat_mul(m, inv, b);
    lemma_inverse_right(m);

    Vec3::<T>::axiom_eqv_reflexive(b);
    crate::vec3::ops::lemma_dot_congruence(
        mat_mul(m, inv).row0, identity::<T>().row0, b, b,
    );
    crate::vec3::ops::lemma_dot_congruence(
        mat_mul(m, inv).row1, identity::<T>().row1, b, b,
    );
    crate::vec3::ops::lemma_dot_congruence(
        mat_mul(m, inv).row2, identity::<T>().row2, b, b,
    );

    lemma_identity_mul_vec(b);

    // Chain x: mat_vec_mul(m, solve).x ≡ dot(MI.row0, b) ≡ dot(I.row0, b) ≡ b.x
    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).x,
        dot(mat_mul(m, inv).row0, b),
        dot(identity::<T>().row0, b),
    );
    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).x,
        dot(identity::<T>().row0, b),
        b.x,
    );
    // Chain y
    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).y,
        dot(mat_mul(m, inv).row1, b),
        dot(identity::<T>().row1, b),
    );
    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).y,
        dot(identity::<T>().row1, b),
        b.y,
    );
    // Chain z
    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).z,
        dot(mat_mul(m, inv).row2, b),
        dot(identity::<T>().row2, b),
    );
    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).z,
        dot(identity::<T>().row2, b),
        b.z,
    );
}

/// Uniqueness: if mat_vec_mul(m, x) ≡ b and det ≠ 0, then x ≡ solve(m, b)
pub proof fn lemma_solve_unique<T: Field>(m: Mat3x3<T>, x: Vec3<T>, b: Vec3<T>)
    requires
        !det(m).eqv(T::zero()),
        mat_vec_mul(m, x).eqv(b),
    ensures
        x.eqv(solve(m, b)),
{
    let inv = inverse(m);

    lemma_mat_vec_mul_mat_mul(inv, m, x);
    lemma_inverse_left(m);

    Vec3::<T>::axiom_eqv_reflexive(x);
    crate::vec3::ops::lemma_dot_congruence(
        mat_mul(inv, m).row0, identity::<T>().row0, x, x,
    );
    crate::vec3::ops::lemma_dot_congruence(
        mat_mul(inv, m).row1, identity::<T>().row1, x, x,
    );
    crate::vec3::ops::lemma_dot_congruence(
        mat_mul(inv, m).row2, identity::<T>().row2, x, x,
    );

    lemma_identity_mul_vec(x);

    // mat_vec_mul(inv, mat_vec_mul(m, x)).i ≡ x.i for each component
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).x,
        dot(mat_mul(inv, m).row0, x),
        dot(identity::<T>().row0, x),
    );
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).x,
        dot(identity::<T>().row0, x),
        x.x,
    );
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).y,
        dot(mat_mul(inv, m).row1, x),
        dot(identity::<T>().row1, x),
    );
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).y,
        dot(identity::<T>().row1, x),
        x.y,
    );
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).z,
        dot(mat_mul(inv, m).row2, x),
        dot(identity::<T>().row2, x),
    );
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).z,
        dot(identity::<T>().row2, x),
        x.z,
    );

    // mat_vec_mul(inv, mat_vec_mul(m, x)) ≡ mat_vec_mul(inv, b) by congruence
    Vec3::<T>::axiom_eqv_reflexive(inv.row0);
    Vec3::<T>::axiom_eqv_reflexive(inv.row1);
    Vec3::<T>::axiom_eqv_reflexive(inv.row2);
    crate::vec3::ops::lemma_dot_congruence(
        inv.row0, inv.row0, mat_vec_mul(m, x), b,
    );
    crate::vec3::ops::lemma_dot_congruence(
        inv.row1, inv.row1, mat_vec_mul(m, x), b,
    );
    crate::vec3::ops::lemma_dot_congruence(
        inv.row2, inv.row2, mat_vec_mul(m, x), b,
    );

    // Chain: x.i ≡ mat_vec_mul(inv, m*x).i ≡ mat_vec_mul(inv, b).i = solve(m,b).i
    T::axiom_eqv_symmetric(mat_vec_mul(inv, mat_vec_mul(m, x)).x, x.x);
    T::axiom_eqv_transitive(
        x.x, mat_vec_mul(inv, mat_vec_mul(m, x)).x, solve(m, b).x,
    );
    T::axiom_eqv_symmetric(mat_vec_mul(inv, mat_vec_mul(m, x)).y, x.y);
    T::axiom_eqv_transitive(
        x.y, mat_vec_mul(inv, mat_vec_mul(m, x)).y, solve(m, b).y,
    );
    T::axiom_eqv_symmetric(mat_vec_mul(inv, mat_vec_mul(m, x)).z, x.z);
    T::axiom_eqv_transitive(
        x.z, mat_vec_mul(inv, mat_vec_mul(m, x)).z, solve(m, b).z,
    );
}

} // verus!
