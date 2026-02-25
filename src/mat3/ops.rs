use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
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

} // verus!
