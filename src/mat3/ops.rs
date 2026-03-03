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

} // verus!
