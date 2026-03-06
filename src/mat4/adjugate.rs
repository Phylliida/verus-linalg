use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::field_lemmas;
use crate::vec3::Vec3;
use crate::vec3::ops::triple;
use crate::vec4::Vec4;
use crate::vec4::ops::{dot, scale};
use super::Mat4x4;
use super::ops::{det, cofactor_vec, transpose, mat_mul, identity,
    mat_vec_mul, drop_x, drop_y, drop_z, drop_w,
    lemma_det_as_dot,
    lemma_det_swap_rows_12, lemma_det_swap_rows_23,
    lemma_dot_e0_right, lemma_dot_e1_right, lemma_dot_e2_right, lemma_dot_e3_right,
    lemma_identity_mul_vec, lemma_mat_vec_mul_mat_mul,
    lemma_det_congruence, lemma_det_identity};
use super::det_advanced::{
    lemma_det_swap_rows_01,
    lemma_det_zero_repeated_row_01, lemma_det_zero_repeated_row_02,
    lemma_det_zero_repeated_row_03};
use super::det_transpose::lemma_det_transpose;
use super::det_multiplicative::lemma_det_multiplicative;

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

// ---------------------------------------------------------------------------
// Helper: triple(a,b,c) ≡ triple(transpose(a,b,c))
// ---------------------------------------------------------------------------

proof fn lemma_triple_transpose<T: Ring>(a: Vec3<T>, b: Vec3<T>, c: Vec3<T>)
    ensures triple(a, b, c).eqv(triple(
        Vec3 { x: a.x, y: b.x, z: c.x },
        Vec3 { x: a.y, y: b.y, z: c.y },
        Vec3 { x: a.z, y: b.z, z: c.z },
    ))
{
    let m = crate::mat3::Mat3x3::<T> { row0: a, row1: b, row2: c };
    crate::mat3::ops::lemma_det_transpose(m);
    T::axiom_eqv_symmetric(
        crate::mat3::ops::det(crate::mat3::ops::transpose(m)),
        crate::mat3::ops::det(m),
    );
}

proof fn lemma_triple_transpose_neg<T: Ring>(a: Vec3<T>, b: Vec3<T>, c: Vec3<T>)
    ensures triple(a, b, c).neg().eqv(triple(
        Vec3 { x: a.x, y: b.x, z: c.x },
        Vec3 { x: a.y, y: b.y, z: c.y },
        Vec3 { x: a.z, y: b.z, z: c.z },
    ).neg())
{
    lemma_triple_transpose(a, b, c);
    T::axiom_neg_congruence(triple(a, b, c), triple(
        Vec3 { x: a.x, y: b.x, z: c.x },
        Vec3 { x: a.y, y: b.y, z: c.y },
        Vec3 { x: a.z, y: b.z, z: c.z },
    ));
}

proof fn lemma_triple_transpose_neg2<T: Ring>(a: Vec3<T>, b: Vec3<T>, c: Vec3<T>)
    ensures triple(a, b, c).neg().neg().eqv(triple(
        Vec3 { x: a.x, y: b.x, z: c.x },
        Vec3 { x: a.y, y: b.y, z: c.y },
        Vec3 { x: a.z, y: b.z, z: c.z },
    ).neg().neg())
{
    lemma_triple_transpose_neg(a, b, c);
    T::axiom_neg_congruence(triple(a, b, c).neg(), triple(
        Vec3 { x: a.x, y: b.x, z: c.x },
        Vec3 { x: a.y, y: b.y, z: c.y },
        Vec3 { x: a.z, y: b.z, z: c.z },
    ).neg());
}

// ---------------------------------------------------------------------------
// adj(m) ≡ transpose(adj(m^T)) row-wise
// ---------------------------------------------------------------------------

pub proof fn lemma_adjugate_transpose_rows<T: Ring>(m: Mat4x4<T>)
    ensures
        adjugate(m).row0.eqv(transpose(adjugate(transpose(m))).row0),
        adjugate(m).row1.eqv(transpose(adjugate(transpose(m))).row1),
        adjugate(m).row2.eqv(transpose(adjugate(transpose(m))).row2),
        adjugate(m).row3.eqv(transpose(adjugate(transpose(m))).row3),
{
    let r0 = m.row0; let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;

    // Row 0: [bare, neg, bare, neg]
    lemma_triple_transpose(drop_x(r1), drop_x(r2), drop_x(r3));
    lemma_triple_transpose_neg(drop_x(r0), drop_x(r2), drop_x(r3));
    lemma_triple_transpose(drop_x(r0), drop_x(r1), drop_x(r3));
    lemma_triple_transpose_neg(drop_x(r0), drop_x(r1), drop_x(r2));

    // Row 1: [neg, double, neg, double]
    lemma_triple_transpose_neg(drop_y(r1), drop_y(r2), drop_y(r3));
    lemma_triple_transpose_neg2(drop_y(r0), drop_y(r2), drop_y(r3));
    lemma_triple_transpose_neg(drop_y(r0), drop_y(r1), drop_y(r3));
    lemma_triple_transpose_neg2(drop_y(r0), drop_y(r1), drop_y(r2));

    // Row 2: [bare, neg, bare, neg]
    lemma_triple_transpose(drop_z(r1), drop_z(r2), drop_z(r3));
    lemma_triple_transpose_neg(drop_z(r0), drop_z(r2), drop_z(r3));
    lemma_triple_transpose(drop_z(r0), drop_z(r1), drop_z(r3));
    lemma_triple_transpose_neg(drop_z(r0), drop_z(r1), drop_z(r2));

    // Row 3: [neg, double, neg, double]
    lemma_triple_transpose_neg(drop_w(r1), drop_w(r2), drop_w(r3));
    lemma_triple_transpose_neg2(drop_w(r0), drop_w(r2), drop_w(r3));
    lemma_triple_transpose_neg(drop_w(r0), drop_w(r1), drop_w(r3));
    lemma_triple_transpose_neg2(drop_w(r0), drop_w(r1), drop_w(r2));
}

// ---------------------------------------------------------------------------
// adj(m) * m = det(m) * I  (left multiply)
// ---------------------------------------------------------------------------

pub proof fn lemma_mat_mul_adjugate_left<T: Ring>(m: Mat4x4<T>)
    ensures
        mat_mul(adjugate(m), m).row0.eqv(
            Vec4 { x: det(m), y: T::zero(), z: T::zero(), w: T::zero() }
        ),
        mat_mul(adjugate(m), m).row1.eqv(
            Vec4 { x: T::zero(), y: det(m), z: T::zero(), w: T::zero() }
        ),
        mat_mul(adjugate(m), m).row2.eqv(
            Vec4 { x: T::zero(), y: T::zero(), z: det(m), w: T::zero() }
        ),
        mat_mul(adjugate(m), m).row3.eqv(
            Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: det(m) }
        ),
{
    let mt = transpose(m);
    let adj = adjugate(m);
    let adj_mt = adjugate(mt);

    lemma_mat_mul_adjugate_right::<T>(mt);
    lemma_adjugate_transpose_rows::<T>(m);
    lemma_det_transpose(m);

    Vec4::<T>::axiom_eqv_reflexive(mt.row0);
    Vec4::<T>::axiom_eqv_reflexive(mt.row1);
    Vec4::<T>::axiom_eqv_reflexive(mt.row2);
    Vec4::<T>::axiom_eqv_reflexive(mt.row3);

    // --- Row 0 ---
    crate::vec4::ops::lemma_dot_congruence(mt.row0, mt.row0, adj.row0, transpose(adj_mt).row0);
    crate::vec4::ops::lemma_dot_congruence(mt.row1, mt.row1, adj.row0, transpose(adj_mt).row0);
    crate::vec4::ops::lemma_dot_congruence(mt.row2, mt.row2, adj.row0, transpose(adj_mt).row0);
    crate::vec4::ops::lemma_dot_congruence(mt.row3, mt.row3, adj.row0, transpose(adj_mt).row0);

    crate::vec4::ops::lemma_dot_commutative(adj.row0, mt.row0);
    T::axiom_eqv_transitive(dot(adj.row0, mt.row0), dot(mt.row0, adj.row0), dot(mt.row0, transpose(adj_mt).row0));
    T::axiom_eqv_transitive(dot(adj.row0, mt.row0), dot(mt.row0, transpose(adj_mt).row0), det(mt));
    T::axiom_eqv_transitive(dot(adj.row0, mt.row0), det(mt), det(m));

    crate::vec4::ops::lemma_dot_commutative(adj.row0, mt.row1);
    T::axiom_eqv_transitive(dot(adj.row0, mt.row1), dot(mt.row1, adj.row0), dot(mt.row1, transpose(adj_mt).row0));
    T::axiom_eqv_transitive(dot(adj.row0, mt.row1), dot(mt.row1, transpose(adj_mt).row0), T::zero());

    crate::vec4::ops::lemma_dot_commutative(adj.row0, mt.row2);
    T::axiom_eqv_transitive(dot(adj.row0, mt.row2), dot(mt.row2, adj.row0), dot(mt.row2, transpose(adj_mt).row0));
    T::axiom_eqv_transitive(dot(adj.row0, mt.row2), dot(mt.row2, transpose(adj_mt).row0), T::zero());

    crate::vec4::ops::lemma_dot_commutative(adj.row0, mt.row3);
    T::axiom_eqv_transitive(dot(adj.row0, mt.row3), dot(mt.row3, adj.row0), dot(mt.row3, transpose(adj_mt).row0));
    T::axiom_eqv_transitive(dot(adj.row0, mt.row3), dot(mt.row3, transpose(adj_mt).row0), T::zero());

    // --- Row 1 ---
    crate::vec4::ops::lemma_dot_congruence(mt.row0, mt.row0, adj.row1, transpose(adj_mt).row1);
    crate::vec4::ops::lemma_dot_congruence(mt.row1, mt.row1, adj.row1, transpose(adj_mt).row1);
    crate::vec4::ops::lemma_dot_congruence(mt.row2, mt.row2, adj.row1, transpose(adj_mt).row1);
    crate::vec4::ops::lemma_dot_congruence(mt.row3, mt.row3, adj.row1, transpose(adj_mt).row1);

    crate::vec4::ops::lemma_dot_commutative(adj.row1, mt.row0);
    T::axiom_eqv_transitive(dot(adj.row1, mt.row0), dot(mt.row0, adj.row1), dot(mt.row0, transpose(adj_mt).row1));
    T::axiom_eqv_transitive(dot(adj.row1, mt.row0), dot(mt.row0, transpose(adj_mt).row1), T::zero());

    crate::vec4::ops::lemma_dot_commutative(adj.row1, mt.row1);
    T::axiom_eqv_transitive(dot(adj.row1, mt.row1), dot(mt.row1, adj.row1), dot(mt.row1, transpose(adj_mt).row1));
    T::axiom_eqv_transitive(dot(adj.row1, mt.row1), dot(mt.row1, transpose(adj_mt).row1), det(mt));
    T::axiom_eqv_transitive(dot(adj.row1, mt.row1), det(mt), det(m));

    crate::vec4::ops::lemma_dot_commutative(adj.row1, mt.row2);
    T::axiom_eqv_transitive(dot(adj.row1, mt.row2), dot(mt.row2, adj.row1), dot(mt.row2, transpose(adj_mt).row1));
    T::axiom_eqv_transitive(dot(adj.row1, mt.row2), dot(mt.row2, transpose(adj_mt).row1), T::zero());

    crate::vec4::ops::lemma_dot_commutative(adj.row1, mt.row3);
    T::axiom_eqv_transitive(dot(adj.row1, mt.row3), dot(mt.row3, adj.row1), dot(mt.row3, transpose(adj_mt).row1));
    T::axiom_eqv_transitive(dot(adj.row1, mt.row3), dot(mt.row3, transpose(adj_mt).row1), T::zero());

    // --- Row 2 ---
    crate::vec4::ops::lemma_dot_congruence(mt.row0, mt.row0, adj.row2, transpose(adj_mt).row2);
    crate::vec4::ops::lemma_dot_congruence(mt.row1, mt.row1, adj.row2, transpose(adj_mt).row2);
    crate::vec4::ops::lemma_dot_congruence(mt.row2, mt.row2, adj.row2, transpose(adj_mt).row2);
    crate::vec4::ops::lemma_dot_congruence(mt.row3, mt.row3, adj.row2, transpose(adj_mt).row2);

    crate::vec4::ops::lemma_dot_commutative(adj.row2, mt.row0);
    T::axiom_eqv_transitive(dot(adj.row2, mt.row0), dot(mt.row0, adj.row2), dot(mt.row0, transpose(adj_mt).row2));
    T::axiom_eqv_transitive(dot(adj.row2, mt.row0), dot(mt.row0, transpose(adj_mt).row2), T::zero());

    crate::vec4::ops::lemma_dot_commutative(adj.row2, mt.row1);
    T::axiom_eqv_transitive(dot(adj.row2, mt.row1), dot(mt.row1, adj.row2), dot(mt.row1, transpose(adj_mt).row2));
    T::axiom_eqv_transitive(dot(adj.row2, mt.row1), dot(mt.row1, transpose(adj_mt).row2), T::zero());

    crate::vec4::ops::lemma_dot_commutative(adj.row2, mt.row2);
    T::axiom_eqv_transitive(dot(adj.row2, mt.row2), dot(mt.row2, adj.row2), dot(mt.row2, transpose(adj_mt).row2));
    T::axiom_eqv_transitive(dot(adj.row2, mt.row2), dot(mt.row2, transpose(adj_mt).row2), det(mt));
    T::axiom_eqv_transitive(dot(adj.row2, mt.row2), det(mt), det(m));

    crate::vec4::ops::lemma_dot_commutative(adj.row2, mt.row3);
    T::axiom_eqv_transitive(dot(adj.row2, mt.row3), dot(mt.row3, adj.row2), dot(mt.row3, transpose(adj_mt).row2));
    T::axiom_eqv_transitive(dot(adj.row2, mt.row3), dot(mt.row3, transpose(adj_mt).row2), T::zero());

    // --- Row 3 ---
    crate::vec4::ops::lemma_dot_congruence(mt.row0, mt.row0, adj.row3, transpose(adj_mt).row3);
    crate::vec4::ops::lemma_dot_congruence(mt.row1, mt.row1, adj.row3, transpose(adj_mt).row3);
    crate::vec4::ops::lemma_dot_congruence(mt.row2, mt.row2, adj.row3, transpose(adj_mt).row3);
    crate::vec4::ops::lemma_dot_congruence(mt.row3, mt.row3, adj.row3, transpose(adj_mt).row3);

    crate::vec4::ops::lemma_dot_commutative(adj.row3, mt.row0);
    T::axiom_eqv_transitive(dot(adj.row3, mt.row0), dot(mt.row0, adj.row3), dot(mt.row0, transpose(adj_mt).row3));
    T::axiom_eqv_transitive(dot(adj.row3, mt.row0), dot(mt.row0, transpose(adj_mt).row3), T::zero());

    crate::vec4::ops::lemma_dot_commutative(adj.row3, mt.row1);
    T::axiom_eqv_transitive(dot(adj.row3, mt.row1), dot(mt.row1, adj.row3), dot(mt.row1, transpose(adj_mt).row3));
    T::axiom_eqv_transitive(dot(adj.row3, mt.row1), dot(mt.row1, transpose(adj_mt).row3), T::zero());

    crate::vec4::ops::lemma_dot_commutative(adj.row3, mt.row2);
    T::axiom_eqv_transitive(dot(adj.row3, mt.row2), dot(mt.row2, adj.row3), dot(mt.row2, transpose(adj_mt).row3));
    T::axiom_eqv_transitive(dot(adj.row3, mt.row2), dot(mt.row2, transpose(adj_mt).row3), T::zero());

    crate::vec4::ops::lemma_dot_commutative(adj.row3, mt.row3);
    T::axiom_eqv_transitive(dot(adj.row3, mt.row3), dot(mt.row3, adj.row3), dot(mt.row3, transpose(adj_mt).row3));
    T::axiom_eqv_transitive(dot(adj.row3, mt.row3), dot(mt.row3, transpose(adj_mt).row3), det(mt));
    T::axiom_eqv_transitive(dot(adj.row3, mt.row3), det(mt), det(m));
}

// ---------------------------------------------------------------------------
// inverse(m) * m = I  (left inverse)
// ---------------------------------------------------------------------------

pub proof fn lemma_inverse_left<T: Field>(m: Mat4x4<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        mat_mul(inverse(m), m).row0.eqv(identity::<T>().row0),
        mat_mul(inverse(m), m).row1.eqv(identity::<T>().row1),
        mat_mul(inverse(m), m).row2.eqv(identity::<T>().row2),
        mat_mul(inverse(m), m).row3.eqv(identity::<T>().row3),
{
    let d = det(m);
    let d_inv = d.recip();
    let adj = adjugate(m);
    let inv = inverse(m);
    let mt = transpose(m);

    lemma_mat_mul_adjugate_left(m);

    // Factor d_inv out of each of 16 dot products via dot_scale_left
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row0, mt.row0);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row0, mt.row1);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row0, mt.row2);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row0, mt.row3);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row1, mt.row0);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row1, mt.row1);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row1, mt.row2);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row1, mt.row3);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row2, mt.row0);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row2, mt.row1);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row2, mt.row2);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row2, mt.row3);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row3, mt.row0);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row3, mt.row1);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row3, mt.row2);
    crate::vec4::ops::lemma_dot_scale_left(d_inv, adj.row3, mt.row3);

    // d_inv * d ≡ 1
    field_lemmas::lemma_mul_recip_left::<T>(d);

    // --- Diagonal entries: d_inv * det(m) ≡ 1 ---

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row0, mt.row0), d);
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row0), d_inv.mul(dot(adj.row0, mt.row0)), d_inv.mul(d));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row0), d_inv.mul(d), T::one());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row1, mt.row1), d);
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row1), d_inv.mul(dot(adj.row1, mt.row1)), d_inv.mul(d));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row1), d_inv.mul(d), T::one());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row2, mt.row2), d);
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row2), d_inv.mul(dot(adj.row2, mt.row2)), d_inv.mul(d));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row2), d_inv.mul(d), T::one());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row3, mt.row3), d);
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row3), mt.row3), d_inv.mul(dot(adj.row3, mt.row3)), d_inv.mul(d));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row3), mt.row3), d_inv.mul(d), T::one());

    // --- Off-diagonal entries: d_inv * 0 ≡ 0 ---
    T::axiom_mul_zero_right(d_inv);

    // Row 0
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row0, mt.row1), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row1), d_inv.mul(dot(adj.row0, mt.row1)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row1), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row0, mt.row2), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row2), d_inv.mul(dot(adj.row0, mt.row2)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row2), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row0, mt.row3), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row3), d_inv.mul(dot(adj.row0, mt.row3)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row0), mt.row3), d_inv.mul(T::zero()), T::zero());

    // Row 1
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row1, mt.row0), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row0), d_inv.mul(dot(adj.row1, mt.row0)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row0), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row1, mt.row2), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row2), d_inv.mul(dot(adj.row1, mt.row2)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row2), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row1, mt.row3), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row3), d_inv.mul(dot(adj.row1, mt.row3)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row1), mt.row3), d_inv.mul(T::zero()), T::zero());

    // Row 2
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row2, mt.row0), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row0), d_inv.mul(dot(adj.row2, mt.row0)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row0), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row2, mt.row1), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row1), d_inv.mul(dot(adj.row2, mt.row1)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row1), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row2, mt.row3), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row3), d_inv.mul(dot(adj.row2, mt.row3)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row2), mt.row3), d_inv.mul(T::zero()), T::zero());

    // Row 3
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row3, mt.row0), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row3), mt.row0), d_inv.mul(dot(adj.row3, mt.row0)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row3), mt.row0), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row3, mt.row1), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row3), mt.row1), d_inv.mul(dot(adj.row3, mt.row1)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row3), mt.row1), d_inv.mul(T::zero()), T::zero());

    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row3, mt.row2), T::zero());
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row3), mt.row2), d_inv.mul(dot(adj.row3, mt.row2)), d_inv.mul(T::zero()));
    T::axiom_eqv_transitive(dot(scale(d_inv, adj.row3), mt.row2), d_inv.mul(T::zero()), T::zero());
}

// ---------------------------------------------------------------------------
// Field-level helpers
// ---------------------------------------------------------------------------

pub proof fn lemma_recip_nonzero<T: Field>(d: T)
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

pub proof fn lemma_det_inverse<T: Field>(m: Mat4x4<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        det(inverse(m)).eqv(det(m).recip()),
{
    let d = det(m);
    let inv = inverse(m);

    lemma_inverse_right(m);
    lemma_det_congruence(mat_mul(m, inv), identity::<T>());
    lemma_det_identity::<T>();
    T::axiom_eqv_transitive(det(mat_mul(m, inv)), det(identity::<T>()), T::one());

    lemma_det_multiplicative(m, inv);
    T::axiom_eqv_symmetric(det(mat_mul(m, inv)), d.mul(det(inv)));
    T::axiom_eqv_transitive(d.mul(det(inv)), det(mat_mul(m, inv)), T::one());

    field_lemmas::lemma_recip_unique::<T>(d, det(inv));
}

pub proof fn lemma_det_inv_nonzero<T: Field>(m: Mat4x4<T>)
    requires !det(m).eqv(T::zero()),
    ensures !det(inverse(m)).eqv(T::zero()),
{
    lemma_det_inverse(m);
    lemma_recip_nonzero::<T>(det(m));
    if det(inverse(m)).eqv(T::zero()) {
        T::axiom_eqv_symmetric(det(inverse(m)), det(m).recip());
        T::axiom_eqv_transitive(det(m).recip(), det(inverse(m)), T::zero());
    }
}

// ---------------------------------------------------------------------------
// inv(m) * (m * v) ≡ v
// ---------------------------------------------------------------------------

pub proof fn lemma_inv_m_cancel_left<T: Field>(m: Mat4x4<T>, v: Vec4<T>)
    requires !det(m).eqv(T::zero()),
    ensures mat_vec_mul(inverse(m), mat_vec_mul(m, v)).eqv(v),
{
    let inv = inverse(m);
    lemma_inverse_left(m);
    lemma_mat_vec_mul_mat_mul(inv, m, v);

    Vec4::<T>::axiom_eqv_reflexive(v);
    crate::vec4::ops::lemma_dot_congruence(
        mat_mul(inv, m).row0, identity::<T>().row0, v, v);
    crate::vec4::ops::lemma_dot_congruence(
        mat_mul(inv, m).row1, identity::<T>().row1, v, v);
    crate::vec4::ops::lemma_dot_congruence(
        mat_mul(inv, m).row2, identity::<T>().row2, v, v);
    crate::vec4::ops::lemma_dot_congruence(
        mat_mul(inv, m).row3, identity::<T>().row3, v, v);

    lemma_identity_mul_vec(v);

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

    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, v)).w,
        mat_vec_mul(mat_mul(inv, m), v).w,
        mat_vec_mul(identity(), v).w);
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, v)).w,
        mat_vec_mul(identity(), v).w, v.w);
}

// ---------------------------------------------------------------------------
// Solve: x = M^{-1} b
// ---------------------------------------------------------------------------

pub open spec fn solve<T: Field>(m: Mat4x4<T>, b: Vec4<T>) -> Vec4<T> {
    mat_vec_mul(inverse(m), b)
}

pub proof fn lemma_solve_correct<T: Field>(m: Mat4x4<T>, b: Vec4<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        mat_vec_mul(m, solve(m, b)).eqv(b),
{
    let inv = inverse(m);

    lemma_mat_vec_mul_mat_mul(m, inv, b);
    lemma_inverse_right(m);

    Vec4::<T>::axiom_eqv_reflexive(b);
    crate::vec4::ops::lemma_dot_congruence(
        mat_mul(m, inv).row0, identity::<T>().row0, b, b);
    crate::vec4::ops::lemma_dot_congruence(
        mat_mul(m, inv).row1, identity::<T>().row1, b, b);
    crate::vec4::ops::lemma_dot_congruence(
        mat_mul(m, inv).row2, identity::<T>().row2, b, b);
    crate::vec4::ops::lemma_dot_congruence(
        mat_mul(m, inv).row3, identity::<T>().row3, b, b);

    lemma_identity_mul_vec(b);

    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).x,
        dot(mat_mul(m, inv).row0, b),
        dot(identity::<T>().row0, b));
    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).x,
        dot(identity::<T>().row0, b), b.x);

    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).y,
        dot(mat_mul(m, inv).row1, b),
        dot(identity::<T>().row1, b));
    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).y,
        dot(identity::<T>().row1, b), b.y);

    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).z,
        dot(mat_mul(m, inv).row2, b),
        dot(identity::<T>().row2, b));
    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).z,
        dot(identity::<T>().row2, b), b.z);

    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).w,
        dot(mat_mul(m, inv).row3, b),
        dot(identity::<T>().row3, b));
    T::axiom_eqv_transitive(
        mat_vec_mul(m, solve(m, b)).w,
        dot(identity::<T>().row3, b), b.w);
}

pub proof fn lemma_solve_unique<T: Field>(m: Mat4x4<T>, x: Vec4<T>, b: Vec4<T>)
    requires
        !det(m).eqv(T::zero()),
        mat_vec_mul(m, x).eqv(b),
    ensures
        x.eqv(solve(m, b)),
{
    let inv = inverse(m);

    lemma_mat_vec_mul_mat_mul(inv, m, x);
    lemma_inverse_left(m);

    Vec4::<T>::axiom_eqv_reflexive(x);
    crate::vec4::ops::lemma_dot_congruence(
        mat_mul(inv, m).row0, identity::<T>().row0, x, x);
    crate::vec4::ops::lemma_dot_congruence(
        mat_mul(inv, m).row1, identity::<T>().row1, x, x);
    crate::vec4::ops::lemma_dot_congruence(
        mat_mul(inv, m).row2, identity::<T>().row2, x, x);
    crate::vec4::ops::lemma_dot_congruence(
        mat_mul(inv, m).row3, identity::<T>().row3, x, x);

    lemma_identity_mul_vec(x);

    // mat_vec_mul(inv, mat_vec_mul(m, x)).i ≡ x.i
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).x,
        dot(mat_mul(inv, m).row0, x),
        dot(identity::<T>().row0, x));
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).x,
        dot(identity::<T>().row0, x), x.x);

    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).y,
        dot(mat_mul(inv, m).row1, x),
        dot(identity::<T>().row1, x));
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).y,
        dot(identity::<T>().row1, x), x.y);

    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).z,
        dot(mat_mul(inv, m).row2, x),
        dot(identity::<T>().row2, x));
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).z,
        dot(identity::<T>().row2, x), x.z);

    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).w,
        dot(mat_mul(inv, m).row3, x),
        dot(identity::<T>().row3, x));
    T::axiom_eqv_transitive(
        mat_vec_mul(inv, mat_vec_mul(m, x)).w,
        dot(identity::<T>().row3, x), x.w);

    // mat_vec_mul(inv, m*x) ≡ mat_vec_mul(inv, b) via congruence
    Vec4::<T>::axiom_eqv_reflexive(inv.row0);
    Vec4::<T>::axiom_eqv_reflexive(inv.row1);
    Vec4::<T>::axiom_eqv_reflexive(inv.row2);
    Vec4::<T>::axiom_eqv_reflexive(inv.row3);
    crate::vec4::ops::lemma_dot_congruence(
        inv.row0, inv.row0, mat_vec_mul(m, x), b);
    crate::vec4::ops::lemma_dot_congruence(
        inv.row1, inv.row1, mat_vec_mul(m, x), b);
    crate::vec4::ops::lemma_dot_congruence(
        inv.row2, inv.row2, mat_vec_mul(m, x), b);
    crate::vec4::ops::lemma_dot_congruence(
        inv.row3, inv.row3, mat_vec_mul(m, x), b);

    // Chain: x.i ≡ mat_vec_mul(inv, m*x).i ≡ solve(m, b).i
    T::axiom_eqv_symmetric(mat_vec_mul(inv, mat_vec_mul(m, x)).x, x.x);
    T::axiom_eqv_transitive(
        x.x, mat_vec_mul(inv, mat_vec_mul(m, x)).x, solve(m, b).x);

    T::axiom_eqv_symmetric(mat_vec_mul(inv, mat_vec_mul(m, x)).y, x.y);
    T::axiom_eqv_transitive(
        x.y, mat_vec_mul(inv, mat_vec_mul(m, x)).y, solve(m, b).y);

    T::axiom_eqv_symmetric(mat_vec_mul(inv, mat_vec_mul(m, x)).z, x.z);
    T::axiom_eqv_transitive(
        x.z, mat_vec_mul(inv, mat_vec_mul(m, x)).z, solve(m, b).z);

    T::axiom_eqv_symmetric(mat_vec_mul(inv, mat_vec_mul(m, x)).w, x.w);
    T::axiom_eqv_transitive(
        x.w, mat_vec_mul(inv, mat_vec_mul(m, x)).w, solve(m, b).w);
}

// ---------------------------------------------------------------------------
// inverse(inverse(m)) ≡ m
// ---------------------------------------------------------------------------

pub proof fn lemma_inverse_involution<T: Field>(m: Mat4x4<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        inverse(inverse(m)).row0.eqv(m.row0),
        inverse(inverse(m)).row1.eqv(m.row1),
        inverse(inverse(m)).row2.eqv(m.row2),
        inverse(inverse(m)).row3.eqv(m.row3),
{
    let inv = inverse(m);
    let inv2 = inverse(inv);

    lemma_det_inv_nonzero(m);

    let e0 = Vec4::<T> { x: T::one(), y: T::zero(), z: T::zero(), w: T::zero() };
    let e1 = Vec4::<T> { x: T::zero(), y: T::one(), z: T::zero(), w: T::zero() };
    let e2 = Vec4::<T> { x: T::zero(), y: T::zero(), z: T::one(), w: T::zero() };
    let e3 = Vec4::<T> { x: T::zero(), y: T::zero(), z: T::zero(), w: T::one() };

    lemma_inv_m_cancel_left(m, e0);
    lemma_inv_m_cancel_left(m, e1);
    lemma_inv_m_cancel_left(m, e2);
    lemma_inv_m_cancel_left(m, e3);

    lemma_solve_unique(inv, mat_vec_mul(m, e0), e0);
    lemma_solve_unique(inv, mat_vec_mul(m, e1), e1);
    lemma_solve_unique(inv, mat_vec_mul(m, e2), e2);
    lemma_solve_unique(inv, mat_vec_mul(m, e3), e3);

    // dot(v, e_j) ≡ v.{j} for all rows of m and inv2
    lemma_dot_e0_right(m.row0); lemma_dot_e0_right(m.row1);
    lemma_dot_e0_right(m.row2); lemma_dot_e0_right(m.row3);
    lemma_dot_e0_right(inv2.row0); lemma_dot_e0_right(inv2.row1);
    lemma_dot_e0_right(inv2.row2); lemma_dot_e0_right(inv2.row3);

    lemma_dot_e1_right(m.row0); lemma_dot_e1_right(m.row1);
    lemma_dot_e1_right(m.row2); lemma_dot_e1_right(m.row3);
    lemma_dot_e1_right(inv2.row0); lemma_dot_e1_right(inv2.row1);
    lemma_dot_e1_right(inv2.row2); lemma_dot_e1_right(inv2.row3);

    lemma_dot_e2_right(m.row0); lemma_dot_e2_right(m.row1);
    lemma_dot_e2_right(m.row2); lemma_dot_e2_right(m.row3);
    lemma_dot_e2_right(inv2.row0); lemma_dot_e2_right(inv2.row1);
    lemma_dot_e2_right(inv2.row2); lemma_dot_e2_right(inv2.row3);

    lemma_dot_e3_right(m.row0); lemma_dot_e3_right(m.row1);
    lemma_dot_e3_right(m.row2); lemma_dot_e3_right(m.row3);
    lemma_dot_e3_right(inv2.row0); lemma_dot_e3_right(inv2.row1);
    lemma_dot_e3_right(inv2.row2); lemma_dot_e3_right(inv2.row3);

    // Row 0: chain m.row0.{j} ≡ dot(m.row0, e_j) ≡ dot(inv2.row0, e_j) ≡ inv2.row0.{j}
    // Column 0
    T::axiom_eqv_symmetric(dot(m.row0, e0), m.row0.x);
    T::axiom_eqv_transitive(m.row0.x, dot(m.row0, e0), dot(inv2.row0, e0));
    T::axiom_eqv_transitive(m.row0.x, dot(inv2.row0, e0), inv2.row0.x);
    T::axiom_eqv_symmetric(m.row0.x, inv2.row0.x);
    // Column 1
    T::axiom_eqv_symmetric(dot(m.row0, e1), m.row0.y);
    T::axiom_eqv_transitive(m.row0.y, dot(m.row0, e1), dot(inv2.row0, e1));
    T::axiom_eqv_transitive(m.row0.y, dot(inv2.row0, e1), inv2.row0.y);
    T::axiom_eqv_symmetric(m.row0.y, inv2.row0.y);
    // Column 2
    T::axiom_eqv_symmetric(dot(m.row0, e2), m.row0.z);
    T::axiom_eqv_transitive(m.row0.z, dot(m.row0, e2), dot(inv2.row0, e2));
    T::axiom_eqv_transitive(m.row0.z, dot(inv2.row0, e2), inv2.row0.z);
    T::axiom_eqv_symmetric(m.row0.z, inv2.row0.z);
    // Column 3
    T::axiom_eqv_symmetric(dot(m.row0, e3), m.row0.w);
    T::axiom_eqv_transitive(m.row0.w, dot(m.row0, e3), dot(inv2.row0, e3));
    T::axiom_eqv_transitive(m.row0.w, dot(inv2.row0, e3), inv2.row0.w);
    T::axiom_eqv_symmetric(m.row0.w, inv2.row0.w);

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

    T::axiom_eqv_symmetric(dot(m.row1, e3), m.row1.w);
    T::axiom_eqv_transitive(m.row1.w, dot(m.row1, e3), dot(inv2.row1, e3));
    T::axiom_eqv_transitive(m.row1.w, dot(inv2.row1, e3), inv2.row1.w);
    T::axiom_eqv_symmetric(m.row1.w, inv2.row1.w);

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

    T::axiom_eqv_symmetric(dot(m.row2, e3), m.row2.w);
    T::axiom_eqv_transitive(m.row2.w, dot(m.row2, e3), dot(inv2.row2, e3));
    T::axiom_eqv_transitive(m.row2.w, dot(inv2.row2, e3), inv2.row2.w);
    T::axiom_eqv_symmetric(m.row2.w, inv2.row2.w);

    // Row 3
    T::axiom_eqv_symmetric(dot(m.row3, e0), m.row3.x);
    T::axiom_eqv_transitive(m.row3.x, dot(m.row3, e0), dot(inv2.row3, e0));
    T::axiom_eqv_transitive(m.row3.x, dot(inv2.row3, e0), inv2.row3.x);
    T::axiom_eqv_symmetric(m.row3.x, inv2.row3.x);

    T::axiom_eqv_symmetric(dot(m.row3, e1), m.row3.y);
    T::axiom_eqv_transitive(m.row3.y, dot(m.row3, e1), dot(inv2.row3, e1));
    T::axiom_eqv_transitive(m.row3.y, dot(inv2.row3, e1), inv2.row3.y);
    T::axiom_eqv_symmetric(m.row3.y, inv2.row3.y);

    T::axiom_eqv_symmetric(dot(m.row3, e2), m.row3.z);
    T::axiom_eqv_transitive(m.row3.z, dot(m.row3, e2), dot(inv2.row3, e2));
    T::axiom_eqv_transitive(m.row3.z, dot(inv2.row3, e2), inv2.row3.z);
    T::axiom_eqv_symmetric(m.row3.z, inv2.row3.z);

    T::axiom_eqv_symmetric(dot(m.row3, e3), m.row3.w);
    T::axiom_eqv_transitive(m.row3.w, dot(m.row3, e3), dot(inv2.row3, e3));
    T::axiom_eqv_transitive(m.row3.w, dot(inv2.row3, e3), inv2.row3.w);
    T::axiom_eqv_symmetric(m.row3.w, inv2.row3.w);
}

} // verus!
