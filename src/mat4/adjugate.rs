use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::field_lemmas;
use crate::vec4::Vec4;
use crate::vec4::ops::{dot, scale};
use super::Mat4x4;
use super::ops::{det, cofactor_vec, transpose, mat_mul, identity,
    lemma_det_as_dot,
    lemma_det_swap_rows_12, lemma_det_swap_rows_23};
use super::det_advanced::{
    lemma_det_swap_rows_01,
    lemma_det_zero_repeated_row_01, lemma_det_zero_repeated_row_02,
    lemma_det_zero_repeated_row_03};

verus! {

// ---------------------------------------------------------------------------
// Spec functions
// ---------------------------------------------------------------------------

/// Adjugate (classical adjoint) of a 4×4 matrix.
/// Defined as the transpose of the cofactor matrix.
pub open spec fn adjugate<T: Ring>(m: Mat4x4<T>) -> Mat4x4<T> {
    let cv0 = cofactor_vec(m.row1, m.row2, m.row3);
    let cv1 = cofactor_vec(m.row0, m.row2, m.row3);
    let cv2 = cofactor_vec(m.row0, m.row1, m.row3);
    let cv3 = cofactor_vec(m.row0, m.row1, m.row2);
    // Transpose of [cv0, -cv1, cv2, -cv3]
    Mat4x4 {
        row0: Vec4 { x: cv0.x, y: cv1.x.neg(), z: cv2.x, w: cv3.x.neg() },
        row1: Vec4 { x: cv0.y, y: cv1.y.neg(), z: cv2.y, w: cv3.y.neg() },
        row2: Vec4 { x: cv0.z, y: cv1.z.neg(), z: cv2.z, w: cv3.z.neg() },
        row3: Vec4 { x: cv0.w, y: cv1.w.neg(), z: cv2.w, w: cv3.w.neg() },
    }
}

/// Inverse of a 4×4 matrix: (1/det) * adjugate.
pub open spec fn inverse<T: Field>(m: Mat4x4<T>) -> Mat4x4<T> {
    let d_inv = det(m).recip();
    let adj = adjugate(m);
    Mat4x4 {
        row0: scale(d_inv, adj.row0),
        row1: scale(d_inv, adj.row1),
        row2: scale(d_inv, adj.row2),
        row3: scale(d_inv, adj.row3),
    }
}

// ---------------------------------------------------------------------------
// Helpers for off-diagonal zeros
// ---------------------------------------------------------------------------

/// dot(r, cofactor_vec(a, b, c)) ≡ 0 when det(r, a, b, c) ≡ 0
proof fn lemma_dot_cv_zero<T: Ring>(r: Vec4<T>, a: Vec4<T>, b: Vec4<T>, c: Vec4<T>)
    requires det(Mat4x4 { row0: r, row1: a, row2: b, row3: c }).eqv(T::zero())
    ensures dot(r, cofactor_vec(a, b, c)).eqv(T::zero())
{
    let m = Mat4x4 { row0: r, row1: a, row2: b, row3: c };
    lemma_det_as_dot(m);
    T::axiom_eqv_symmetric(det(m), dot(r, cofactor_vec(a, b, c)));
    T::axiom_eqv_transitive(dot(r, cofactor_vec(a, b, c)), det(m), T::zero());
}

/// dot(r, cofactor_vec(a, b, c).neg()) ≡ 0 when det(r, a, b, c) ≡ 0
proof fn lemma_dot_cv_neg_zero<T: Ring>(r: Vec4<T>, a: Vec4<T>, b: Vec4<T>, c: Vec4<T>)
    requires det(Mat4x4 { row0: r, row1: a, row2: b, row3: c }).eqv(T::zero())
    ensures dot(r, cofactor_vec(a, b, c).neg()).eqv(T::zero())
{
    lemma_dot_cv_zero(r, a, b, c);
    let cv = cofactor_vec(a, b, c);
    crate::vec4::ops::lemma_dot_neg_right(r, cv);
    T::axiom_neg_congruence(dot(r, cv), T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(dot(r, cv).neg(), T::zero().neg(), T::zero());
    T::axiom_eqv_transitive(dot(r, cv.neg()), dot(r, cv).neg(), T::zero());
}

// ---------------------------------------------------------------------------
// m * adj(m) = det(m) * I  (right multiply)
// ---------------------------------------------------------------------------

/// Row 0 of m * adj(m) ≡ (det(m), 0, 0, 0)
proof fn lemma_adjugate_right_row0<T: Ring>(m: Mat4x4<T>)
    ensures
        mat_mul(m, adjugate(m)).row0.eqv(
            Vec4 { x: det(m), y: T::zero(), z: T::zero(), w: T::zero() }
        ),
{
    let r0 = m.row0; let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;

    // (0,0): dot(r0, cv(r1,r2,r3)) ≡ det(m)
    lemma_det_as_dot(m);
    T::axiom_eqv_symmetric(det(m), dot(r0, cofactor_vec(r1, r2, r3)));

    // (0,1): dot(r0, cv(r0,r2,r3).neg()) ≡ 0  (rows 0,1 equal in {r0,r0,r2,r3})
    lemma_det_zero_repeated_row_01(r0, r2, r3);
    lemma_dot_cv_neg_zero(r0, r0, r2, r3);

    // (0,2): dot(r0, cv(r0,r1,r3)) ≡ 0  (rows 0,1 equal in {r0,r0,r1,r3})
    lemma_det_zero_repeated_row_01(r0, r1, r3);
    lemma_dot_cv_zero(r0, r0, r1, r3);

    // (0,3): dot(r0, cv(r0,r1,r2).neg()) ≡ 0  (rows 0,1 equal in {r0,r0,r1,r2})
    lemma_det_zero_repeated_row_01(r0, r1, r2);
    lemma_dot_cv_neg_zero(r0, r0, r1, r2);
}

/// Row 1 of m * adj(m) ≡ (0, det(m), 0, 0)
proof fn lemma_adjugate_right_row1<T: Ring>(m: Mat4x4<T>)
    ensures
        mat_mul(m, adjugate(m)).row1.eqv(
            Vec4 { x: T::zero(), y: det(m), z: T::zero(), w: T::zero() }
        ),
{
    let r0 = m.row0; let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;
    let cv1 = cofactor_vec(r0, r2, r3);

    // (1,0): dot(r1, cv(r1,r2,r3)) ≡ 0
    lemma_det_zero_repeated_row_01(r1, r2, r3);
    lemma_dot_cv_zero(r1, r1, r2, r3);

    // (1,1): dot(r1, cv1.neg()) ≡ det(m)
    //   dot(r1, cv1.neg()) ≡ -dot(r1, cv1)
    crate::vec4::ops::lemma_dot_neg_right(r1, cv1);
    //   det(r1,r0,r2,r3) ≡ dot(r1, cv1)
    let m_1023 = Mat4x4 { row0: r1, row1: r0, row2: r2, row3: r3 };
    lemma_det_as_dot(m_1023);
    T::axiom_eqv_symmetric(det(m_1023), dot(r1, cv1));
    //   swap_01: det(r1,r0,r2,r3) ≡ det(m).neg()
    lemma_det_swap_rows_01(m);
    //   dot(r1, cv1) ≡ det(m_1023) ≡ det(m).neg()
    T::axiom_eqv_transitive(dot(r1, cv1), det(m_1023), det(m).neg());
    //   dot(r1, cv1).neg() ≡ det(m).neg().neg() ≡ det(m)
    T::axiom_neg_congruence(dot(r1, cv1), det(m).neg());
    additive_group_lemmas::lemma_neg_involution(det(m));
    T::axiom_eqv_transitive(dot(r1, cv1).neg(), det(m).neg().neg(), det(m));
    T::axiom_eqv_transitive(dot(r1, cv1.neg()), dot(r1, cv1).neg(), det(m));

    // (1,2): dot(r1, cv(r0,r1,r3)) ≡ 0  (rows 0,2 equal in {r1,r0,r1,r3})
    lemma_det_zero_repeated_row_02(r1, r0, r3);
    lemma_dot_cv_zero(r1, r0, r1, r3);

    // (1,3): dot(r1, cv(r0,r1,r2).neg()) ≡ 0  (rows 0,2 equal in {r1,r0,r1,r2})
    lemma_det_zero_repeated_row_02(r1, r0, r2);
    lemma_dot_cv_neg_zero(r1, r0, r1, r2);
}

/// Row 2 of m * adj(m) ≡ (0, 0, det(m), 0)
proof fn lemma_adjugate_right_row2<T: Ring>(m: Mat4x4<T>)
    ensures
        mat_mul(m, adjugate(m)).row2.eqv(
            Vec4 { x: T::zero(), y: T::zero(), z: det(m), w: T::zero() }
        ),
{
    let r0 = m.row0; let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;
    let cv2 = cofactor_vec(r0, r1, r3);

    // (2,0): dot(r2, cv(r1,r2,r3)) ≡ 0  (rows 0,2 equal in {r2,r1,r2,r3})
    lemma_det_zero_repeated_row_02(r2, r1, r3);
    lemma_dot_cv_zero(r2, r1, r2, r3);

    // (2,1): dot(r2, cv(r0,r2,r3).neg()) ≡ 0  (rows 0,2 equal in {r2,r0,r2,r3})
    lemma_det_zero_repeated_row_02(r2, r0, r3);
    lemma_dot_cv_neg_zero(r2, r0, r2, r3);

    // (2,2): dot(r2, cv2) ≡ det(m)
    //   det_as_dot on {r2,r0,r1,r3}: det(r2,r0,r1,r3) ≡ dot(r2, cv2)
    let m_2013 = Mat4x4 { row0: r2, row1: r0, row2: r1, row3: r3 };
    lemma_det_as_dot(m_2013);
    T::axiom_eqv_symmetric(det(m_2013), dot(r2, cv2));
    //   Two swaps: det(r2,r0,r1,r3) → det(r0,r2,r1,r3) → det(r0,r1,r2,r3) = det(m)
    let m_0213 = Mat4x4 { row0: r0, row1: r2, row2: r1, row3: r3 };
    lemma_det_swap_rows_01(m_2013);
    // det(m_0213) ≡ det(m_2013).neg()
    lemma_det_swap_rows_12(m_0213);
    // det(m) ≡ det(m_0213).neg()
    //   Chain: det(m) ≡ det(m_0213).neg() ≡ det(m_2013).neg().neg() ≡ det(m_2013)
    T::axiom_neg_congruence(det(m_0213), det(m_2013).neg());
    additive_group_lemmas::lemma_neg_involution(det(m_2013));
    T::axiom_eqv_transitive(det(m_0213).neg(), det(m_2013).neg().neg(), det(m_2013));
    T::axiom_eqv_transitive(det(m), det(m_0213).neg(), det(m_2013));
    //   dot(r2, cv2) ≡ det(m_2013) ≡ det(m)
    T::axiom_eqv_symmetric(det(m), det(m_2013));
    T::axiom_eqv_transitive(dot(r2, cv2), det(m_2013), det(m));

    // (2,3): dot(r2, cv(r0,r1,r2).neg()) ≡ 0  (rows 0,3 equal in {r2,r0,r1,r2})
    lemma_det_zero_repeated_row_03(r2, r0, r1);
    lemma_dot_cv_neg_zero(r2, r0, r1, r2);
}

/// Row 3 of m * adj(m) ≡ (0, 0, 0, det(m))
proof fn lemma_adjugate_right_row3<T: Ring>(m: Mat4x4<T>)
    ensures
        mat_mul(m, adjugate(m)).row3.eqv(
            Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: det(m) }
        ),
{
    let r0 = m.row0; let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;
    let cv3 = cofactor_vec(r0, r1, r2);

    // (3,0): dot(r3, cv(r1,r2,r3)) ≡ 0  (rows 0,3 equal in {r3,r1,r2,r3})
    lemma_det_zero_repeated_row_03(r3, r1, r2);
    lemma_dot_cv_zero(r3, r1, r2, r3);

    // (3,1): dot(r3, cv(r0,r2,r3).neg()) ≡ 0  (rows 0,3 equal in {r3,r0,r2,r3})
    lemma_det_zero_repeated_row_03(r3, r0, r2);
    lemma_dot_cv_neg_zero(r3, r0, r2, r3);

    // (3,2): dot(r3, cv(r0,r1,r3)) ≡ 0  (rows 0,3 equal in {r3,r0,r1,r3})
    lemma_det_zero_repeated_row_03(r3, r0, r1);
    lemma_dot_cv_zero(r3, r0, r1, r3);

    // (3,3): dot(r3, cv3.neg()) ≡ det(m)
    //   dot(r3, cv3.neg()) ≡ -dot(r3, cv3)
    crate::vec4::ops::lemma_dot_neg_right(r3, cv3);
    //   det_as_dot on {r3,r0,r1,r2}: det(r3,r0,r1,r2) ≡ dot(r3, cv3)
    let m_3012 = Mat4x4 { row0: r3, row1: r0, row2: r1, row3: r2 };
    lemma_det_as_dot(m_3012);
    T::axiom_eqv_symmetric(det(m_3012), dot(r3, cv3));
    //   Three swaps to show det(r3,r0,r1,r2) ≡ det(m).neg()
    let m_0312 = Mat4x4 { row0: r0, row1: r3, row2: r1, row3: r2 };
    let m_0132 = Mat4x4 { row0: r0, row1: r1, row2: r3, row3: r2 };
    lemma_det_swap_rows_01(m_3012);
    // det(m_0312) ≡ det(m_3012).neg()
    lemma_det_swap_rows_12(m_0312);
    // det(m_0132) ≡ det(m_0312).neg()
    lemma_det_swap_rows_23(m_0132);
    // det(m) ≡ det(m_0132).neg()
    //   Chain: det(m) ≡ det(m_0132).neg() → det(m_0132) ≡ det(m_0312).neg()
    //   → det(m_0132).neg() ≡ det(m_0312).neg().neg() ≡ det(m_0312)
    T::axiom_neg_congruence(det(m_0132), det(m_0312).neg());
    additive_group_lemmas::lemma_neg_involution(det(m_0312));
    T::axiom_eqv_transitive(det(m_0132).neg(), det(m_0312).neg().neg(), det(m_0312));
    T::axiom_eqv_transitive(det(m), det(m_0132).neg(), det(m_0312));
    //   det(m) ≡ det(m_0312) ≡ det(m_3012).neg()
    T::axiom_eqv_transitive(det(m), det(m_0312), det(m_3012).neg());
    //   det(m_3012) ≡ det(m).neg()
    T::axiom_neg_congruence(det(m), det(m_3012).neg());
    additive_group_lemmas::lemma_neg_involution(det(m_3012));
    T::axiom_eqv_transitive(det(m).neg(), det(m_3012).neg().neg(), det(m_3012));
    T::axiom_eqv_symmetric(det(m).neg(), det(m_3012));
    //   dot(r3, cv3) ≡ det(m_3012) ≡ det(m).neg()
    T::axiom_eqv_transitive(dot(r3, cv3), det(m_3012), det(m).neg());
    //   dot(r3, cv3).neg() ≡ det(m).neg().neg() ≡ det(m)
    T::axiom_neg_congruence(dot(r3, cv3), det(m).neg());
    additive_group_lemmas::lemma_neg_involution(det(m));
    T::axiom_eqv_transitive(dot(r3, cv3).neg(), det(m).neg().neg(), det(m));
    //   dot(r3, cv3.neg()) ≡ dot(r3, cv3).neg() ≡ det(m)
    T::axiom_eqv_transitive(dot(r3, cv3.neg()), dot(r3, cv3).neg(), det(m));
}

/// m * adjugate(m) has det(m) on diagonal, 0 off-diagonal.
pub proof fn lemma_mat_mul_adjugate_right<T: Ring>(m: Mat4x4<T>)
    ensures
        mat_mul(m, adjugate(m)).row0.eqv(
            Vec4 { x: det(m), y: T::zero(), z: T::zero(), w: T::zero() }
        ),
        mat_mul(m, adjugate(m)).row1.eqv(
            Vec4 { x: T::zero(), y: det(m), z: T::zero(), w: T::zero() }
        ),
        mat_mul(m, adjugate(m)).row2.eqv(
            Vec4 { x: T::zero(), y: T::zero(), z: det(m), w: T::zero() }
        ),
        mat_mul(m, adjugate(m)).row3.eqv(
            Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: det(m) }
        ),
{
    lemma_adjugate_right_row0(m);
    lemma_adjugate_right_row1(m);
    lemma_adjugate_right_row2(m);
    lemma_adjugate_right_row3(m);
}

// ---------------------------------------------------------------------------
// m * inverse(m) = I  (right inverse)
// ---------------------------------------------------------------------------

/// m * inverse(m) ≡ I when det(m) ≢ 0.
pub proof fn lemma_inverse_right<T: Field>(m: Mat4x4<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        mat_mul(m, inverse(m)).row0.eqv(identity::<T>().row0),
        mat_mul(m, inverse(m)).row1.eqv(identity::<T>().row1),
        mat_mul(m, inverse(m)).row2.eqv(identity::<T>().row2),
        mat_mul(m, inverse(m)).row3.eqv(identity::<T>().row3),
{
    let d = det(m);
    let d_inv = d.recip();
    let adj = adjugate(m);
    let inv = inverse(m);
    let t_inv = transpose(inv);
    let t_adj = transpose(adj);

    // transpose(inv).row_j = scale(d_inv, transpose(adj).row_j) structurally.
    // So dot(m.row_i, t_inv.row_j) ≡ d_inv * dot(m.row_i, t_adj.row_j) via dot_scale_right.

    lemma_mat_mul_adjugate_right(m);

    // d_inv * d ≡ 1
    field_lemmas::lemma_mul_recip_left::<T>(d);

    // Factor d_inv out of each of 16 dot products
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row0, t_adj.row0);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row0, t_adj.row1);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row0, t_adj.row2);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row0, t_adj.row3);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row1, t_adj.row0);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row1, t_adj.row1);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row1, t_adj.row2);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row1, t_adj.row3);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row2, t_adj.row0);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row2, t_adj.row1);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row2, t_adj.row2);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row2, t_adj.row3);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row3, t_adj.row0);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row3, t_adj.row1);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row3, t_adj.row2);
    crate::vec4::ops::lemma_dot_scale_right(d_inv, m.row3, t_adj.row3);

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

    // (3,3)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row3, t_adj.row3), d);
    T::axiom_eqv_transitive(dot(m.row3, t_inv.row3), d_inv.mul(dot(m.row3, t_adj.row3)), d_inv.mul(d));
    T::axiom_eqv_transitive(dot(m.row3, t_inv.row3), d_inv.mul(d), T::one());

    // --- Off-diagonal entries: d_inv * 0 ≡ 0 ---
    T::axiom_mul_zero_right(d_inv);

    // Row 0: (0,1), (0,2), (0,3)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row0, t_adj.row1), T::zero());
    T::axiom_eqv_transitive(dot(m.row0, t_inv.row1), d_inv.mul(dot(m.row0, t_adj.row1)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row0, t_inv.row1), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row0, t_adj.row2), T::zero());
    T::axiom_eqv_transitive(dot(m.row0, t_inv.row2), d_inv.mul(dot(m.row0, t_adj.row2)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row0, t_inv.row2), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row0, t_adj.row3), T::zero());
    T::axiom_eqv_transitive(dot(m.row0, t_inv.row3), d_inv.mul(dot(m.row0, t_adj.row3)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row0, t_inv.row3), d_inv.mul(T::zero()), T::zero());

    // Row 1: (1,0), (1,2), (1,3)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row1, t_adj.row0), T::zero());
    T::axiom_eqv_transitive(dot(m.row1, t_inv.row0), d_inv.mul(dot(m.row1, t_adj.row0)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row1, t_inv.row0), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row1, t_adj.row2), T::zero());
    T::axiom_eqv_transitive(dot(m.row1, t_inv.row2), d_inv.mul(dot(m.row1, t_adj.row2)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row1, t_inv.row2), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row1, t_adj.row3), T::zero());
    T::axiom_eqv_transitive(dot(m.row1, t_inv.row3), d_inv.mul(dot(m.row1, t_adj.row3)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row1, t_inv.row3), d_inv.mul(T::zero()), T::zero());

    // Row 2: (2,0), (2,1), (2,3)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row2, t_adj.row0), T::zero());
    T::axiom_eqv_transitive(dot(m.row2, t_inv.row0), d_inv.mul(dot(m.row2, t_adj.row0)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row2, t_inv.row0), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row2, t_adj.row1), T::zero());
    T::axiom_eqv_transitive(dot(m.row2, t_inv.row1), d_inv.mul(dot(m.row2, t_adj.row1)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row2, t_inv.row1), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row2, t_adj.row3), T::zero());
    T::axiom_eqv_transitive(dot(m.row2, t_inv.row3), d_inv.mul(dot(m.row2, t_adj.row3)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row2, t_inv.row3), d_inv.mul(T::zero()), T::zero());

    // Row 3: (3,0), (3,1), (3,2)
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row3, t_adj.row0), T::zero());
    T::axiom_eqv_transitive(dot(m.row3, t_inv.row0), d_inv.mul(dot(m.row3, t_adj.row0)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row3, t_inv.row0), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row3, t_adj.row1), T::zero());
    T::axiom_eqv_transitive(dot(m.row3, t_inv.row1), d_inv.mul(dot(m.row3, t_adj.row1)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row3, t_inv.row1), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row3, t_adj.row2), T::zero());
    T::axiom_eqv_transitive(dot(m.row3, t_inv.row2), d_inv.mul(dot(m.row3, t_adj.row2)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(m.row3, t_inv.row2), d_inv.mul(T::zero()), T::zero());
}

} // verus!
