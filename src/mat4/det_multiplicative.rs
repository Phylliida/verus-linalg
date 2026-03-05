use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use crate::vec3::Vec3;
use crate::vec3::ops::cross;
use crate::vec4::Vec4;
use crate::vec4::ops::scale;
use super::Mat4x4;
use super::ops::{det, mat_mul, cofactor_vec, drop_x, drop_y, drop_z, drop_w,
    lemma_det_linear_first_row, lemma_det_linear_second_row, lemma_det_linear_third_row, lemma_det_linear_fourth_row,
    lemma_det_scale_first_row, lemma_det_scale_second_row, lemma_det_scale_third_row, lemma_det_scale_fourth_row,
    lemma_det_zero_repeated_row_12, lemma_det_zero_repeated_row_13, lemma_det_zero_repeated_row_23,
    lemma_det_swap_rows_12, lemma_det_swap_rows_13, lemma_det_swap_rows_23,
    lemma_factor_4, lemma_add_congruence_4,
};
use super::det_advanced::{
    lemma_det_zero_repeated_row_01, lemma_det_zero_repeated_row_02, lemma_det_zero_repeated_row_03,
    lemma_det_swap_rows_01, lemma_det_swap_rows_02, lemma_det_swap_rows_03,
};
use crate::mat3::ops::{lemma_mul_zero_by_eqv, lemma_add_congruence_3, lemma_factor_3};

verus! {

// ===========================================================================
// Section 1: Sum4 kill helpers
// Kill zero terms from left-associated 4-term sums: ((a+b)+c)+d
// ===========================================================================

/// Kill first: a≡0 → ((a+b)+c)+d ≡ (b+c)+d
pub proof fn lemma_sum4_kill_first<T: Ring>(a: T, b: T, c: T, d: T)
    requires a.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(b.add(c).add(d)),
{
    T::axiom_add_congruence_left(a, T::zero(), b);
    additive_group_lemmas::lemma_add_zero_left(b);
    T::axiom_eqv_transitive(a.add(b), T::zero().add(b), b);
    T::axiom_add_congruence_left(a.add(b), b, c);
    T::axiom_add_congruence_left(a.add(b).add(c), b.add(c), d);
}

/// Kill first and second: a≡0, b≡0 → ((a+b)+c)+d ≡ c+d
pub proof fn lemma_sum4_kill_first_second<T: Ring>(a: T, b: T, c: T, d: T)
    requires a.eqv(T::zero()), b.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(c.add(d)),
{
    lemma_sum4_kill_first(a, b, c, d);
    T::axiom_add_congruence_left(b, T::zero(), c);
    additive_group_lemmas::lemma_add_zero_left(c);
    T::axiom_eqv_transitive(b.add(c), T::zero().add(c), c);
    T::axiom_add_congruence_left(b.add(c), c, d);
    T::axiom_eqv_transitive(a.add(b).add(c).add(d), b.add(c).add(d), c.add(d));
}

/// Kill first and third: a≡0, c≡0 → ((a+b)+c)+d ≡ b+d
pub proof fn lemma_sum4_kill_first_third<T: Ring>(a: T, b: T, c: T, d: T)
    requires a.eqv(T::zero()), c.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(b.add(d)),
{
    lemma_sum4_kill_first(a, b, c, d);
    additive_group_lemmas::lemma_add_congruence_right(b, c, T::zero());
    T::axiom_add_zero_right(b);
    T::axiom_eqv_transitive(b.add(c), b.add(T::zero()), b);
    T::axiom_add_congruence_left(b.add(c), b, d);
    T::axiom_eqv_transitive(a.add(b).add(c).add(d), b.add(c).add(d), b.add(d));
}

/// Kill first and fourth: a≡0, d≡0 → ((a+b)+c)+d ≡ b+c
pub proof fn lemma_sum4_kill_first_fourth<T: Ring>(a: T, b: T, c: T, d: T)
    requires a.eqv(T::zero()), d.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(b.add(c)),
{
    lemma_sum4_kill_first(a, b, c, d);
    additive_group_lemmas::lemma_add_congruence_right(b.add(c), d, T::zero());
    T::axiom_add_zero_right(b.add(c));
    T::axiom_eqv_transitive(b.add(c).add(d), b.add(c).add(T::zero()), b.add(c));
    T::axiom_eqv_transitive(a.add(b).add(c).add(d), b.add(c).add(d), b.add(c));
}

/// Kill first, second, third: a≡0, b≡0, c≡0 → ((a+b)+c)+d ≡ d
pub proof fn lemma_sum4_kill_first_second_third<T: Ring>(a: T, b: T, c: T, d: T)
    requires a.eqv(T::zero()), b.eqv(T::zero()), c.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(d),
{
    lemma_sum4_kill_first_second(a, b, c, d);
    T::axiom_add_congruence_left(c, T::zero(), d);
    additive_group_lemmas::lemma_add_zero_left(d);
    T::axiom_eqv_transitive(c.add(d), T::zero().add(d), d);
    T::axiom_eqv_transitive(a.add(b).add(c).add(d), c.add(d), d);
}

/// Kill first, second, fourth: a≡0, b≡0, d≡0 → ((a+b)+c)+d ≡ c
pub proof fn lemma_sum4_kill_first_second_fourth<T: Ring>(a: T, b: T, c: T, d: T)
    requires a.eqv(T::zero()), b.eqv(T::zero()), d.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(c),
{
    lemma_sum4_kill_first_second(a, b, c, d);
    additive_group_lemmas::lemma_add_congruence_right(c, d, T::zero());
    T::axiom_add_zero_right(c);
    T::axiom_eqv_transitive(c.add(d), c.add(T::zero()), c);
    T::axiom_eqv_transitive(a.add(b).add(c).add(d), c.add(d), c);
}

/// Kill first, third, fourth: a≡0, c≡0, d≡0 → ((a+b)+c)+d ≡ b
pub proof fn lemma_sum4_kill_first_third_fourth<T: Ring>(a: T, b: T, c: T, d: T)
    requires a.eqv(T::zero()), c.eqv(T::zero()), d.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(b),
{
    lemma_sum4_kill_first_third(a, b, c, d);
    additive_group_lemmas::lemma_add_congruence_right(b, d, T::zero());
    T::axiom_add_zero_right(b);
    T::axiom_eqv_transitive(b.add(d), b.add(T::zero()), b);
    T::axiom_eqv_transitive(a.add(b).add(c).add(d), b.add(d), b);
}

/// Kill second: b≡0 → ((a+b)+c)+d ≡ (a+c)+d
pub proof fn lemma_sum4_kill_second<T: Ring>(a: T, b: T, c: T, d: T)
    requires b.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(a.add(c).add(d)),
{
    additive_group_lemmas::lemma_add_congruence_right(a, b, T::zero());
    T::axiom_add_zero_right(a);
    T::axiom_eqv_transitive(a.add(b), a.add(T::zero()), a);
    T::axiom_add_congruence_left(a.add(b), a, c);
    T::axiom_add_congruence_left(a.add(b).add(c), a.add(c), d);
}

/// Kill second and third: b≡0, c≡0 → ((a+b)+c)+d ≡ a+d
pub proof fn lemma_sum4_kill_second_third<T: Ring>(a: T, b: T, c: T, d: T)
    requires b.eqv(T::zero()), c.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(a.add(d)),
{
    lemma_sum4_kill_second(a, b, c, d);
    additive_group_lemmas::lemma_add_congruence_right(a, c, T::zero());
    T::axiom_add_zero_right(a);
    T::axiom_eqv_transitive(a.add(c), a.add(T::zero()), a);
    T::axiom_add_congruence_left(a.add(c), a, d);
    T::axiom_eqv_transitive(a.add(b).add(c).add(d), a.add(c).add(d), a.add(d));
}

/// Kill second and fourth: b≡0, d≡0 → ((a+b)+c)+d ≡ a+c
pub proof fn lemma_sum4_kill_second_fourth<T: Ring>(a: T, b: T, c: T, d: T)
    requires b.eqv(T::zero()), d.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(a.add(c)),
{
    lemma_sum4_kill_second(a, b, c, d);
    additive_group_lemmas::lemma_add_congruence_right(a.add(c), d, T::zero());
    T::axiom_add_zero_right(a.add(c));
    T::axiom_eqv_transitive(a.add(c).add(d), a.add(c).add(T::zero()), a.add(c));
    T::axiom_eqv_transitive(a.add(b).add(c).add(d), a.add(c).add(d), a.add(c));
}

/// Kill second, third, fourth: b≡0, c≡0, d≡0 → ((a+b)+c)+d ≡ a
pub proof fn lemma_sum4_kill_second_third_fourth<T: Ring>(a: T, b: T, c: T, d: T)
    requires b.eqv(T::zero()), c.eqv(T::zero()), d.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(a),
{
    lemma_sum4_kill_second_third(a, b, c, d);
    additive_group_lemmas::lemma_add_congruence_right(a, d, T::zero());
    T::axiom_add_zero_right(a);
    T::axiom_eqv_transitive(a.add(d), a.add(T::zero()), a);
    T::axiom_eqv_transitive(a.add(b).add(c).add(d), a.add(d), a);
}

/// Kill third: c≡0 → ((a+b)+c)+d ≡ (a+b)+d
pub proof fn lemma_sum4_kill_third<T: Ring>(a: T, b: T, c: T, d: T)
    requires c.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(a.add(b).add(d)),
{
    additive_group_lemmas::lemma_add_congruence_right(a.add(b), c, T::zero());
    T::axiom_add_zero_right(a.add(b));
    T::axiom_eqv_transitive(a.add(b).add(c), a.add(b).add(T::zero()), a.add(b));
    T::axiom_add_congruence_left(a.add(b).add(c), a.add(b), d);
}

/// Kill third and fourth: c≡0, d≡0 → ((a+b)+c)+d ≡ a+b
pub proof fn lemma_sum4_kill_third_fourth<T: Ring>(a: T, b: T, c: T, d: T)
    requires c.eqv(T::zero()), d.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(a.add(b)),
{
    lemma_sum4_kill_third(a, b, c, d);
    additive_group_lemmas::lemma_add_congruence_right(a.add(b), d, T::zero());
    T::axiom_add_zero_right(a.add(b));
    T::axiom_eqv_transitive(a.add(b).add(d), a.add(b).add(T::zero()), a.add(b));
    T::axiom_eqv_transitive(a.add(b).add(c).add(d), a.add(b).add(d), a.add(b));
}

/// Kill fourth: d≡0 → ((a+b)+c)+d ≡ (a+b)+c
pub proof fn lemma_sum4_kill_fourth<T: Ring>(a: T, b: T, c: T, d: T)
    requires d.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(a.add(b).add(c)),
{
    additive_group_lemmas::lemma_add_congruence_right(a.add(b).add(c), d, T::zero());
    T::axiom_add_zero_right(a.add(b).add(c));
    T::axiom_eqv_transitive(a.add(b).add(c).add(d), a.add(b).add(c).add(T::zero()), a.add(b).add(c));
}

// ===========================================================================
// Section 2: Row expansion helpers
// Expand a 4-term scaled Vec4 sum in a specific row of det into 4 scaled dets
// ===========================================================================

/// Expand det when row 1 (second row) is a 4-term scaled sum.
pub proof fn lemma_det_expand_second_row_4<T: Ring>(
    r0: Vec4<T>,
    s0: T, v0: Vec4<T>, s1: T, v1: Vec4<T>, s2: T, v2: Vec4<T>, s3: T, v3: Vec4<T>,
    r2: Vec4<T>, r3: Vec4<T>,
)
    ensures
        det(Mat4x4 { row0: r0,
            row1: scale(s0, v0).add(scale(s1, v1)).add(scale(s2, v2)).add(scale(s3, v3)),
            row2: r2, row3: r3 }).eqv(
            s0.mul(det(Mat4x4 { row0: r0, row1: v0, row2: r2, row3: r3 }))
              .add(s1.mul(det(Mat4x4 { row0: r0, row1: v1, row2: r2, row3: r3 })))
              .add(s2.mul(det(Mat4x4 { row0: r0, row1: v2, row2: r2, row3: r3 })))
              .add(s3.mul(det(Mat4x4 { row0: r0, row1: v3, row2: r2, row3: r3 })))
        ),
{
    let x = scale(s0, v0);
    let y = scale(s1, v1);
    let z = scale(s2, v2);
    let w = scale(s3, v3);

    // Linearity: split 3 times
    lemma_det_linear_second_row(r0, x.add(y).add(z), w, r2, r3);
    lemma_det_linear_second_row(r0, x.add(y), z, r2, r3);
    lemma_det_linear_second_row(r0, x, y, r2, r3);

    // Scale: pull out scalars
    lemma_det_scale_second_row(s0, r0, v0, r2, r3);
    lemma_det_scale_second_row(s1, r0, v1, r2, r3);
    lemma_det_scale_second_row(s2, r0, v2, r2, r3);
    lemma_det_scale_second_row(s3, r0, v3, r2, r3);

    let d0 = det(Mat4x4 { row0: r0, row1: v0, row2: r2, row3: r3 });
    let d1 = det(Mat4x4 { row0: r0, row1: v1, row2: r2, row3: r3 });
    let d2 = det(Mat4x4 { row0: r0, row1: v2, row2: r2, row3: r3 });
    let d3 = det(Mat4x4 { row0: r0, row1: v3, row2: r2, row3: r3 });
    let dx = det(Mat4x4 { row0: r0, row1: x, row2: r2, row3: r3 });
    let dy = det(Mat4x4 { row0: r0, row1: y, row2: r2, row3: r3 });
    let dz = det(Mat4x4 { row0: r0, row1: z, row2: r2, row3: r3 });
    let dw = det(Mat4x4 { row0: r0, row1: w, row2: r2, row3: r3 });

    // Chain inner pair: dx + dy ≡ s0*d0 + s1*d1
    T::axiom_add_congruence_left(dx, s0.mul(d0), dy);
    additive_group_lemmas::lemma_add_congruence_right(s0.mul(d0), dy, s1.mul(d1));
    T::axiom_eqv_transitive(dx.add(dy), s0.mul(d0).add(dy), s0.mul(d0).add(s1.mul(d1)));

    // det(r0, x+y, ...) ≡ dx+dy ≡ s0*d0 + s1*d1
    let dxy = det(Mat4x4 { row0: r0, row1: x.add(y), row2: r2, row3: r3 });
    T::axiom_eqv_transitive(dxy, dx.add(dy), s0.mul(d0).add(s1.mul(d1)));

    // dxy + dz ≡ (s0*d0+s1*d1) + s2*d2
    T::axiom_add_congruence_left(dxy, s0.mul(d0).add(s1.mul(d1)), dz);
    additive_group_lemmas::lemma_add_congruence_right(
        s0.mul(d0).add(s1.mul(d1)), dz, s2.mul(d2));
    T::axiom_eqv_transitive(dxy.add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)));

    // det(r0, (x+y)+z, ...) ≡ (s0*d0+s1*d1)+s2*d2
    let dxyz = det(Mat4x4 { row0: r0, row1: x.add(y).add(z), row2: r2, row3: r3 });
    T::axiom_eqv_transitive(dxyz, dxy.add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)));

    // dxyz + dw ≡ ((s0*d0+s1*d1)+s2*d2) + s3*d3
    T::axiom_add_congruence_left(dxyz,
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)), dw);
    additive_group_lemmas::lemma_add_congruence_right(
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)), dw, s3.mul(d3));
    T::axiom_eqv_transitive(dxyz.add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(s3.mul(d3)));

    // det(r0, ((x+y)+z)+w, ...) ≡ final 4-term sum
    let dxyzw = det(Mat4x4 { row0: r0, row1: x.add(y).add(z).add(w), row2: r2, row3: r3 });
    T::axiom_eqv_transitive(dxyzw, dxyz.add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(s3.mul(d3)));
}

/// Expand det when row 2 (third row) is a 4-term scaled sum.
pub proof fn lemma_det_expand_third_row_4<T: Ring>(
    r0: Vec4<T>, r1: Vec4<T>,
    s0: T, v0: Vec4<T>, s1: T, v1: Vec4<T>, s2: T, v2: Vec4<T>, s3: T, v3: Vec4<T>,
    r3: Vec4<T>,
)
    ensures
        det(Mat4x4 { row0: r0, row1: r1,
            row2: scale(s0, v0).add(scale(s1, v1)).add(scale(s2, v2)).add(scale(s3, v3)),
            row3: r3 }).eqv(
            s0.mul(det(Mat4x4 { row0: r0, row1: r1, row2: v0, row3: r3 }))
              .add(s1.mul(det(Mat4x4 { row0: r0, row1: r1, row2: v1, row3: r3 })))
              .add(s2.mul(det(Mat4x4 { row0: r0, row1: r1, row2: v2, row3: r3 })))
              .add(s3.mul(det(Mat4x4 { row0: r0, row1: r1, row2: v3, row3: r3 })))
        ),
{
    let x = scale(s0, v0);
    let y = scale(s1, v1);
    let z = scale(s2, v2);
    let w = scale(s3, v3);

    lemma_det_linear_third_row(r0, r1, x.add(y).add(z), w, r3);
    lemma_det_linear_third_row(r0, r1, x.add(y), z, r3);
    lemma_det_linear_third_row(r0, r1, x, y, r3);

    lemma_det_scale_third_row(s0, r0, r1, v0, r3);
    lemma_det_scale_third_row(s1, r0, r1, v1, r3);
    lemma_det_scale_third_row(s2, r0, r1, v2, r3);
    lemma_det_scale_third_row(s3, r0, r1, v3, r3);

    let d0 = det(Mat4x4 { row0: r0, row1: r1, row2: v0, row3: r3 });
    let d1 = det(Mat4x4 { row0: r0, row1: r1, row2: v1, row3: r3 });
    let d2 = det(Mat4x4 { row0: r0, row1: r1, row2: v2, row3: r3 });
    let d3 = det(Mat4x4 { row0: r0, row1: r1, row2: v3, row3: r3 });
    let dx = det(Mat4x4 { row0: r0, row1: r1, row2: x, row3: r3 });
    let dy = det(Mat4x4 { row0: r0, row1: r1, row2: y, row3: r3 });
    let dz = det(Mat4x4 { row0: r0, row1: r1, row2: z, row3: r3 });
    let dw = det(Mat4x4 { row0: r0, row1: r1, row2: w, row3: r3 });

    T::axiom_add_congruence_left(dx, s0.mul(d0), dy);
    additive_group_lemmas::lemma_add_congruence_right(s0.mul(d0), dy, s1.mul(d1));
    T::axiom_eqv_transitive(dx.add(dy), s0.mul(d0).add(dy), s0.mul(d0).add(s1.mul(d1)));

    let dxy = det(Mat4x4 { row0: r0, row1: r1, row2: x.add(y), row3: r3 });
    T::axiom_eqv_transitive(dxy, dx.add(dy), s0.mul(d0).add(s1.mul(d1)));

    T::axiom_add_congruence_left(dxy, s0.mul(d0).add(s1.mul(d1)), dz);
    additive_group_lemmas::lemma_add_congruence_right(
        s0.mul(d0).add(s1.mul(d1)), dz, s2.mul(d2));
    T::axiom_eqv_transitive(dxy.add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)));

    let dxyz = det(Mat4x4 { row0: r0, row1: r1, row2: x.add(y).add(z), row3: r3 });
    T::axiom_eqv_transitive(dxyz, dxy.add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)));

    T::axiom_add_congruence_left(dxyz,
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)), dw);
    additive_group_lemmas::lemma_add_congruence_right(
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)), dw, s3.mul(d3));
    T::axiom_eqv_transitive(dxyz.add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(s3.mul(d3)));

    let dxyzw = det(Mat4x4 { row0: r0, row1: r1, row2: x.add(y).add(z).add(w), row3: r3 });
    T::axiom_eqv_transitive(dxyzw, dxyz.add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(s3.mul(d3)));
}

/// Expand det when row 3 (fourth row) is a 4-term scaled sum.
pub proof fn lemma_det_expand_fourth_row_4<T: Ring>(
    r0: Vec4<T>, r1: Vec4<T>, r2: Vec4<T>,
    s0: T, v0: Vec4<T>, s1: T, v1: Vec4<T>, s2: T, v2: Vec4<T>, s3: T, v3: Vec4<T>,
)
    ensures
        det(Mat4x4 { row0: r0, row1: r1, row2: r2,
            row3: scale(s0, v0).add(scale(s1, v1)).add(scale(s2, v2)).add(scale(s3, v3)) }).eqv(
            s0.mul(det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: v0 }))
              .add(s1.mul(det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: v1 })))
              .add(s2.mul(det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: v2 })))
              .add(s3.mul(det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: v3 })))
        ),
{
    let x = scale(s0, v0);
    let y = scale(s1, v1);
    let z = scale(s2, v2);
    let w = scale(s3, v3);

    lemma_det_linear_fourth_row(r0, r1, r2, x.add(y).add(z), w);
    lemma_det_linear_fourth_row(r0, r1, r2, x.add(y), z);
    lemma_det_linear_fourth_row(r0, r1, r2, x, y);

    lemma_det_scale_fourth_row(s0, r0, r1, r2, v0);
    lemma_det_scale_fourth_row(s1, r0, r1, r2, v1);
    lemma_det_scale_fourth_row(s2, r0, r1, r2, v2);
    lemma_det_scale_fourth_row(s3, r0, r1, r2, v3);

    let d0 = det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: v0 });
    let d1 = det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: v1 });
    let d2 = det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: v2 });
    let d3 = det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: v3 });
    let dx = det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: x });
    let dy = det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: y });
    let dz = det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: z });
    let dw = det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: w });

    T::axiom_add_congruence_left(dx, s0.mul(d0), dy);
    additive_group_lemmas::lemma_add_congruence_right(s0.mul(d0), dy, s1.mul(d1));
    T::axiom_eqv_transitive(dx.add(dy), s0.mul(d0).add(dy), s0.mul(d0).add(s1.mul(d1)));

    let dxy = det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: x.add(y) });
    T::axiom_eqv_transitive(dxy, dx.add(dy), s0.mul(d0).add(s1.mul(d1)));

    T::axiom_add_congruence_left(dxy, s0.mul(d0).add(s1.mul(d1)), dz);
    additive_group_lemmas::lemma_add_congruence_right(
        s0.mul(d0).add(s1.mul(d1)), dz, s2.mul(d2));
    T::axiom_eqv_transitive(dxy.add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)));

    let dxyz = det(Mat4x4 { row0: r0, row1: r1, row2: r2, row3: x.add(y).add(z) });
    T::axiom_eqv_transitive(dxyz, dxy.add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)));

    T::axiom_add_congruence_left(dxyz,
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)), dw);
    additive_group_lemmas::lemma_add_congruence_right(
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)), dw, s3.mul(d3));
    T::axiom_eqv_transitive(dxyz.add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(s3.mul(d3)));

    let dxyzw = det(Mat4x4 { row0: r0, row1: r1, row2: r2,
        row3: x.add(y).add(z).add(w) });
    T::axiom_eqv_transitive(dxyzw, dxyz.add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(s3.mul(d3)));
}

// ===========================================================================
// Section 3: Col0 branch helpers
// Each proves det(b0, b_j, ABr2, ABr3) ≡ cross(dx(a2),dx(a3)).component * db
// ===========================================================================

/// Branch 1: det(b0, b1, ABr2, ABr3) ≡ cross(drop_x(a2), drop_x(a3)).x * det(b)
proof fn lemma_col0_branch1<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row0, row1: b.row1,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cross(drop_x(a.row2), drop_x(a.row3)).x.mul(det(b))),
{
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let a2 = a.row2;
    let a3 = a.row3;
    let ab = mat_mul(a, b);
    let db = det(b);

    // ---- Expand row 2 (ABr2) ----
    lemma_det_expand_third_row_4(b0, b1,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    // Kill terms 0,1 (repeated rows 02, 12)
    lemma_det_zero_repeated_row_02(b0, b1, ab.row3);
    lemma_det_zero_repeated_row_12(b0, b1, ab.row3);
    lemma_mul_zero_by_eqv(a2.x,
        det(Mat4x4 { row0: b0, row1: b1, row2: b0, row3: ab.row3 }));
    lemma_mul_zero_by_eqv(a2.y,
        det(Mat4x4 { row0: b0, row1: b1, row2: b1, row3: ab.row3 }));

    let (t0, t1, t2, t3) = (
        a2.x.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b0, row3: ab.row3 })),
        a2.y.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b1, row3: ab.row3 })),
        a2.z.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b2, row3: ab.row3 })),
        a2.w.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: ab.row3 })),
    );
    lemma_sum4_kill_first_second(t0, t1, t2, t3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b1, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1).add(t2).add(t3), t2.add(t3));

    // ---- Sub-branch 1a: det(b0,b1,b2,ABr3) ≡ a3.w * db ----
    lemma_det_expand_fourth_row_4(b0, b1, b2,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_03(b0, b1, b2);
    lemma_det_zero_repeated_row_13(b0, b1, b2);
    lemma_det_zero_repeated_row_23(b0, b1, b2);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b0, row1: b1, row2: b2, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b0, row1: b1, row2: b2, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b0, row1: b1, row2: b2, row3: b2 }));
    let (u0, u1, u2, u3) = (
        a3.x.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b2, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b2, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b2, row3: b2 })),
        a3.w.mul(db),
    );
    lemma_sum4_kill_first_second_third(u0, u1, u2, u3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b1, row2: b2, row3: ab.row3 }),
        u0.add(u1).add(u2).add(u3), a3.w.mul(db));

    // t2 = a2.z * det(...) ≡ a2.z * (a3.w * db) ≡ (a2.z * a3.w) * db
    ring_lemmas::lemma_mul_congruence_right(a2.z,
        det(Mat4x4 { row0: b0, row1: b1, row2: b2, row3: ab.row3 }),
        a3.w.mul(db));
    T::axiom_mul_associative(a2.z, a3.w, db);
    T::axiom_eqv_symmetric(a2.z.mul(a3.w).mul(db), a2.z.mul(a3.w.mul(db)));
    T::axiom_eqv_transitive(t2, a2.z.mul(a3.w.mul(db)), a2.z.mul(a3.w).mul(db));

    // ---- Sub-branch 1b: det(b0,b1,b3,ABr3) ≡ a3.z * (-db) ----
    lemma_det_expand_fourth_row_4(b0, b1, b3,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_03(b0, b1, b3);
    lemma_det_zero_repeated_row_13(b0, b1, b3);
    lemma_det_zero_repeated_row_23(b0, b1, b3);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b3 }));
    let (v0, v1, v2, v3) = (
        a3.x.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b3 })),
    );
    lemma_sum4_kill_first_second_fourth(v0, v1, v2, v3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: ab.row3 }),
        v0.add(v1).add(v2).add(v3),
        a3.z.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 })));

    // det(b0,b1,b3,b2) ≡ -db by swap_23
    lemma_det_swap_rows_23(b);
    // Chain: a3.z * det(b0,b1,b3,b2) ≡ a3.z * (-db) ≡ -(a3.z * db)
    ring_lemmas::lemma_mul_congruence_right(a3.z,
        det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 }), db.neg());
    ring_lemmas::lemma_mul_neg_right(a3.z, db);
    T::axiom_eqv_transitive(
        a3.z.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 })),
        a3.z.mul(db.neg()), a3.z.mul(db).neg());
    // det(b0,b1,b3,ABr3) ≡ -(a3.z*db)
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: ab.row3 }),
        a3.z.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 })),
        a3.z.mul(db).neg());

    // t3 = a2.w * det(...) ≡ a2.w * (-(a3.z*db)) ≡ -((a2.w*a3.z)*db)
    ring_lemmas::lemma_mul_congruence_right(a2.w,
        det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: ab.row3 }),
        a3.z.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a2.w, a3.z.mul(db));
    T::axiom_eqv_transitive(t3,
        a2.w.mul(a3.z.mul(db).neg()), a2.w.mul(a3.z.mul(db)).neg());
    T::axiom_mul_associative(a2.w, a3.z, db);
    T::axiom_eqv_symmetric(a2.w.mul(a3.z).mul(db), a2.w.mul(a3.z.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(
        a2.w.mul(a3.z.mul(db)), a2.w.mul(a3.z).mul(db));
    T::axiom_eqv_transitive(t3,
        a2.w.mul(a3.z.mul(db)).neg(), a2.w.mul(a3.z).mul(db).neg());

    // ---- Combine: t2 + t3 ≡ (p-q)*db = cross(dx(a2),dx(a3)).x * db ----
    T::axiom_add_congruence_left(t2, a2.z.mul(a3.w).mul(db), t3);
    additive_group_lemmas::lemma_add_congruence_right(
        a2.z.mul(a3.w).mul(db), t3, a2.w.mul(a3.z).mul(db).neg());
    T::axiom_eqv_transitive(t2.add(t3),
        a2.z.mul(a3.w).mul(db).add(t3),
        a2.z.mul(a3.w).mul(db).add(a2.w.mul(a3.z).mul(db).neg()));

    let p = a2.z.mul(a3.w);
    let q = a2.w.mul(a3.z);
    T::axiom_sub_is_add_neg(p.mul(db), q.mul(db));
    T::axiom_eqv_symmetric(
        p.mul(db).sub(q.mul(db)), p.mul(db).add(q.mul(db).neg()));
    ring_lemmas::lemma_sub_mul_right(p, q, db);
    T::axiom_eqv_symmetric(p.sub(q).mul(db), p.mul(db).sub(q.mul(db)));
    T::axiom_eqv_transitive(
        p.mul(db).add(q.mul(db).neg()),
        p.mul(db).sub(q.mul(db)),
        p.sub(q).mul(db));
    T::axiom_eqv_transitive(t2.add(t3),
        p.mul(db).add(q.mul(db).neg()),
        cross(drop_x(a2), drop_x(a3)).x.mul(db));

    // Final chain
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b1, row2: ab.row2, row3: ab.row3 }),
        t2.add(t3),
        cross(drop_x(a2), drop_x(a3)).x.mul(db));
}

/// Branch 2: det(b0, b2, ABr2, ABr3) ≡ cross(drop_x(a2), drop_x(a3)).y * det(b)
/// Note: negative term comes first, needs additive commutative step.
proof fn lemma_col0_branch2<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row0, row1: b.row2,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cross(drop_x(a.row2), drop_x(a.row3)).y.mul(det(b))),
{
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let a2 = a.row2;
    let a3 = a.row3;
    let ab = mat_mul(a, b);
    let db = det(b);

    // ---- Expand row 2 (ABr2) ----
    lemma_det_expand_third_row_4(b0, b2,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    // Kill terms 0,2 (repeated rows 02, 12)
    lemma_det_zero_repeated_row_02(b0, b2, ab.row3);
    lemma_det_zero_repeated_row_12(b0, b2, ab.row3);
    lemma_mul_zero_by_eqv(a2.x,
        det(Mat4x4 { row0: b0, row1: b2, row2: b0, row3: ab.row3 }));
    lemma_mul_zero_by_eqv(a2.z,
        det(Mat4x4 { row0: b0, row1: b2, row2: b2, row3: ab.row3 }));

    let (t0, t1, t2, t3) = (
        a2.x.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b0, row3: ab.row3 })),
        a2.y.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: ab.row3 })),
        a2.z.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b2, row3: ab.row3 })),
        a2.w.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: ab.row3 })),
    );
    lemma_sum4_kill_first_third(t0, t1, t2, t3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b2, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1).add(t2).add(t3), t1.add(t3));

    // ---- Sub-branch 2a: det(b0,b2,b1,ABr3) ≡ a3.w * (-db) ----
    lemma_det_expand_fourth_row_4(b0, b2, b1,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_03(b0, b2, b1);
    lemma_det_zero_repeated_row_23(b0, b2, b1);
    lemma_det_zero_repeated_row_13(b0, b2, b1);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b2 }));
    let (u0, u1, u2, u3) = (
        a3.x.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b3 })),
    );
    lemma_sum4_kill_first_second_third(u0, u1, u2, u3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: ab.row3 }),
        u0.add(u1).add(u2).add(u3),
        a3.w.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b3 })));

    // det(b0,b2,b1,b3) ≡ -db by swap_12
    lemma_det_swap_rows_12(b);
    ring_lemmas::lemma_mul_congruence_right(a3.w,
        det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b3 }), db.neg());
    ring_lemmas::lemma_mul_neg_right(a3.w, db);
    T::axiom_eqv_transitive(
        a3.w.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b3 })),
        a3.w.mul(db.neg()), a3.w.mul(db).neg());
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: ab.row3 }),
        a3.w.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b3 })),
        a3.w.mul(db).neg());

    // t1 = a2.y * det(...) ≡ a2.y * (-(a3.w*db)) ≡ -((a2.y*a3.w)*db)
    ring_lemmas::lemma_mul_congruence_right(a2.y,
        det(Mat4x4 { row0: b0, row1: b2, row2: b1, row3: ab.row3 }),
        a3.w.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a2.y, a3.w.mul(db));
    T::axiom_eqv_transitive(t1,
        a2.y.mul(a3.w.mul(db).neg()), a2.y.mul(a3.w.mul(db)).neg());
    T::axiom_mul_associative(a2.y, a3.w, db);
    T::axiom_eqv_symmetric(a2.y.mul(a3.w).mul(db), a2.y.mul(a3.w.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(
        a2.y.mul(a3.w.mul(db)), a2.y.mul(a3.w).mul(db));
    T::axiom_eqv_transitive(t1,
        a2.y.mul(a3.w.mul(db)).neg(), a2.y.mul(a3.w).mul(db).neg());

    // ---- Sub-branch 2b: det(b0,b2,b3,ABr3) ≡ a3.y * db ----
    lemma_det_expand_fourth_row_4(b0, b2, b3,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_03(b0, b2, b3);
    lemma_det_zero_repeated_row_13(b0, b2, b3);
    lemma_det_zero_repeated_row_23(b0, b2, b3);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: b2 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: b3 }));
    let (w0, w1, w2, w3) = (
        a3.x.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: b3 })),
    );
    lemma_sum4_kill_first_third_fourth(w0, w1, w2, w3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: ab.row3 }),
        w0.add(w1).add(w2).add(w3),
        a3.y.mul(det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: b1 })));

    // det(b0,b2,b3,b1) ≡ db by double swap: swap_12 then swap_23
    let m_swap = Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b3 };
    // swap_12(b) already called above: det(m_swap) ≡ db.neg()
    lemma_det_swap_rows_23(m_swap);
    // det(b0,b2,b3,b1) ≡ det(m_swap).neg()
    additive_group_lemmas::lemma_neg_congruence(det(m_swap), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m_swap).neg(), db.neg().neg(), db);
    let d_2b = det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: b1 });
    T::axiom_eqv_transitive(d_2b, det(m_swap).neg(), db);

    // det(b0,b2,b3,ABr3) ≡ a3.y * db
    ring_lemmas::lemma_mul_congruence_right(a3.y, d_2b, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: ab.row3 }),
        a3.y.mul(d_2b), a3.y.mul(db));

    // t3 = a2.w * det(...) ≡ a2.w * (a3.y * db) ≡ (a2.w * a3.y) * db
    ring_lemmas::lemma_mul_congruence_right(a2.w,
        det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: ab.row3 }),
        a3.y.mul(db));
    T::axiom_mul_associative(a2.w, a3.y, db);
    T::axiom_eqv_symmetric(a2.w.mul(a3.y).mul(db), a2.w.mul(a3.y.mul(db)));
    T::axiom_eqv_transitive(t3, a2.w.mul(a3.y.mul(db)), a2.w.mul(a3.y).mul(db));

    // ---- Combine: t1 + t3, negative first → commute ----
    T::axiom_add_congruence_left(t1, a2.y.mul(a3.w).mul(db).neg(), t3);
    additive_group_lemmas::lemma_add_congruence_right(
        a2.y.mul(a3.w).mul(db).neg(), t3, a2.w.mul(a3.y).mul(db));
    T::axiom_eqv_transitive(t1.add(t3),
        a2.y.mul(a3.w).mul(db).neg().add(t3),
        a2.y.mul(a3.w).mul(db).neg().add(a2.w.mul(a3.y).mul(db)));

    // Commute: -(q*db) + p*db → p*db + (-(q*db))
    let p = a2.w.mul(a3.y);
    let q = a2.y.mul(a3.w);
    T::axiom_add_commutative(q.mul(db).neg(), p.mul(db));
    T::axiom_eqv_transitive(t1.add(t3),
        q.mul(db).neg().add(p.mul(db)),
        p.mul(db).add(q.mul(db).neg()));

    // Factor: p*db + (-(q*db)) ≡ (p-q)*db
    T::axiom_sub_is_add_neg(p.mul(db), q.mul(db));
    T::axiom_eqv_symmetric(
        p.mul(db).sub(q.mul(db)), p.mul(db).add(q.mul(db).neg()));
    ring_lemmas::lemma_sub_mul_right(p, q, db);
    T::axiom_eqv_symmetric(p.sub(q).mul(db), p.mul(db).sub(q.mul(db)));
    T::axiom_eqv_transitive(
        p.mul(db).add(q.mul(db).neg()),
        p.mul(db).sub(q.mul(db)),
        p.sub(q).mul(db));
    T::axiom_eqv_transitive(t1.add(t3),
        p.mul(db).add(q.mul(db).neg()),
        cross(drop_x(a2), drop_x(a3)).y.mul(db));

    // Final chain
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b2, row2: ab.row2, row3: ab.row3 }),
        t1.add(t3),
        cross(drop_x(a2), drop_x(a3)).y.mul(db));
}

/// Branch 3: det(b0, b3, ABr2, ABr3) ≡ cross(drop_x(a2), drop_x(a3)).z * det(b)
proof fn lemma_col0_branch3<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row0, row1: b.row3,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cross(drop_x(a.row2), drop_x(a.row3)).z.mul(det(b))),
{
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let a2 = a.row2;
    let a3 = a.row3;
    let ab = mat_mul(a, b);
    let db = det(b);

    // ---- Expand row 2 (ABr2) ----
    lemma_det_expand_third_row_4(b0, b3,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    // Kill terms 0,3 (repeated rows 02, 12)
    lemma_det_zero_repeated_row_02(b0, b3, ab.row3);
    lemma_det_zero_repeated_row_12(b0, b3, ab.row3);
    lemma_mul_zero_by_eqv(a2.x,
        det(Mat4x4 { row0: b0, row1: b3, row2: b0, row3: ab.row3 }));
    lemma_mul_zero_by_eqv(a2.w,
        det(Mat4x4 { row0: b0, row1: b3, row2: b3, row3: ab.row3 }));

    let (t0, t1, t2, t3) = (
        a2.x.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b0, row3: ab.row3 })),
        a2.y.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: ab.row3 })),
        a2.z.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: ab.row3 })),
        a2.w.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b3, row3: ab.row3 })),
    );
    lemma_sum4_kill_first_fourth(t0, t1, t2, t3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b3, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1).add(t2).add(t3), t1.add(t2));

    // ---- Sub-branch 3a: det(b0,b3,b1,ABr3) ≡ a3.z * db ----
    lemma_det_expand_fourth_row_4(b0, b3, b1,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_03(b0, b3, b1);
    lemma_det_zero_repeated_row_23(b0, b3, b1);
    lemma_det_zero_repeated_row_13(b0, b3, b1);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: b3 }));
    let (u0, u1, u2, u3) = (
        a3.x.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: b3 })),
    );
    lemma_sum4_kill_first_second_fourth(u0, u1, u2, u3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: ab.row3 }),
        u0.add(u1).add(u2).add(u3),
        a3.z.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: b2 })));

    // det(b0,b3,b1,b2) ≡ db by double swap: swap_23 then swap_12
    lemma_det_swap_rows_23(b);
    let m_swap = Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 };
    // det(m_swap) ≡ db.neg()
    lemma_det_swap_rows_12(m_swap);
    // det(b0,b3,b1,b2) ≡ det(m_swap).neg()
    additive_group_lemmas::lemma_neg_congruence(det(m_swap), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m_swap).neg(), db.neg().neg(), db);
    let d_3a = det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: b2 });
    T::axiom_eqv_transitive(d_3a, det(m_swap).neg(), db);

    // det(b0,b3,b1,ABr3) ≡ a3.z * db
    ring_lemmas::lemma_mul_congruence_right(a3.z, d_3a, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: ab.row3 }),
        a3.z.mul(d_3a), a3.z.mul(db));

    // t1 = a2.y * det(...) ≡ a2.y * (a3.z * db) ≡ (a2.y * a3.z) * db
    ring_lemmas::lemma_mul_congruence_right(a2.y,
        det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: ab.row3 }),
        a3.z.mul(db));
    T::axiom_mul_associative(a2.y, a3.z, db);
    T::axiom_eqv_symmetric(a2.y.mul(a3.z).mul(db), a2.y.mul(a3.z.mul(db)));
    T::axiom_eqv_transitive(t1, a2.y.mul(a3.z.mul(db)), a2.y.mul(a3.z).mul(db));

    // ---- Sub-branch 3b: det(b0,b3,b2,ABr3) ≡ a3.y * (-db) ----
    lemma_det_expand_fourth_row_4(b0, b3, b2,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_03(b0, b3, b2);
    lemma_det_zero_repeated_row_23(b0, b3, b2);
    lemma_det_zero_repeated_row_13(b0, b3, b2);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: b2 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: b3 }));
    let (w0, w1, w2, w3) = (
        a3.x.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: b3 })),
    );
    lemma_sum4_kill_first_third_fourth(w0, w1, w2, w3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: ab.row3 }),
        w0.add(w1).add(w2).add(w3),
        a3.y.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: b1 })));

    // det(b0,b3,b2,b1) ≡ -db by swap_13
    lemma_det_swap_rows_13(b);
    ring_lemmas::lemma_mul_congruence_right(a3.y,
        det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: b1 }), db.neg());
    ring_lemmas::lemma_mul_neg_right(a3.y, db);
    T::axiom_eqv_transitive(
        a3.y.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: b1 })),
        a3.y.mul(db.neg()), a3.y.mul(db).neg());
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: ab.row3 }),
        a3.y.mul(det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: b1 })),
        a3.y.mul(db).neg());

    // t2 = a2.z * det(...) ≡ a2.z * (-(a3.y*db)) ≡ -((a2.z*a3.y)*db)
    ring_lemmas::lemma_mul_congruence_right(a2.z,
        det(Mat4x4 { row0: b0, row1: b3, row2: b2, row3: ab.row3 }),
        a3.y.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a2.z, a3.y.mul(db));
    T::axiom_eqv_transitive(t2,
        a2.z.mul(a3.y.mul(db).neg()), a2.z.mul(a3.y.mul(db)).neg());
    T::axiom_mul_associative(a2.z, a3.y, db);
    T::axiom_eqv_symmetric(a2.z.mul(a3.y).mul(db), a2.z.mul(a3.y.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(
        a2.z.mul(a3.y.mul(db)), a2.z.mul(a3.y).mul(db));
    T::axiom_eqv_transitive(t2,
        a2.z.mul(a3.y.mul(db)).neg(), a2.z.mul(a3.y).mul(db).neg());

    // ---- Combine: t1 + t2 ≡ (p-q)*db = cross(dx(a2),dx(a3)).z * db ----
    T::axiom_add_congruence_left(t1, a2.y.mul(a3.z).mul(db), t2);
    additive_group_lemmas::lemma_add_congruence_right(
        a2.y.mul(a3.z).mul(db), t2, a2.z.mul(a3.y).mul(db).neg());
    T::axiom_eqv_transitive(t1.add(t2),
        a2.y.mul(a3.z).mul(db).add(t2),
        a2.y.mul(a3.z).mul(db).add(a2.z.mul(a3.y).mul(db).neg()));

    let p = a2.y.mul(a3.z);
    let q = a2.z.mul(a3.y);
    T::axiom_sub_is_add_neg(p.mul(db), q.mul(db));
    T::axiom_eqv_symmetric(
        p.mul(db).sub(q.mul(db)), p.mul(db).add(q.mul(db).neg()));
    ring_lemmas::lemma_sub_mul_right(p, q, db);
    T::axiom_eqv_symmetric(p.sub(q).mul(db), p.mul(db).sub(q.mul(db)));
    T::axiom_eqv_transitive(
        p.mul(db).add(q.mul(db).neg()),
        p.mul(db).sub(q.mul(db)),
        p.sub(q).mul(db));
    T::axiom_eqv_transitive(t1.add(t2),
        p.mul(db).add(q.mul(db).neg()),
        cross(drop_x(a2), drop_x(a3)).z.mul(db));

    // Final chain
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b3, row2: ab.row2, row3: ab.row3 }),
        t1.add(t2),
        cross(drop_x(a2), drop_x(a3)).z.mul(db));
}

// ===========================================================================
// Section 4: Col0 main
// det(b0, ABr1, ABr2, ABr3) ≡ cofactor_vec(a1,a2,a3).x * det(b)
// ===========================================================================

/// Column 0 of det multiplicative:
/// det(b0, ABr1, ABr2, ABr3) ≡ cofactor_vec(a1, a2, a3).x * det(b)
pub proof fn lemma_det_mul_col0<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row0, row1: mat_mul(a,b).row1,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cofactor_vec(a.row1, a.row2, a.row3).x.mul(det(b))),
{
    let a1 = a.row1;
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let ab = mat_mul(a, b);
    let db = det(b);
    let cx = cross(drop_x(a.row2), drop_x(a.row3));

    // Expand row 1 (ABr1) → 4 terms
    lemma_det_expand_second_row_4(b0,
        a1.x, b0, a1.y, b1, a1.z, b2, a1.w, b3, ab.row2, ab.row3);

    // Kill first (repeated rows 01)
    lemma_det_zero_repeated_row_01(b0, ab.row2, ab.row3);
    lemma_mul_zero_by_eqv(a1.x,
        det(Mat4x4 { row0: b0, row1: b0, row2: ab.row2, row3: ab.row3 }));

    let (e0, e1, e2, e3) = (
        a1.x.mul(det(Mat4x4 { row0: b0, row1: b0, row2: ab.row2, row3: ab.row3 })),
        a1.y.mul(det(Mat4x4 { row0: b0, row1: b1, row2: ab.row2, row3: ab.row3 })),
        a1.z.mul(det(Mat4x4 { row0: b0, row1: b2, row2: ab.row2, row3: ab.row3 })),
        a1.w.mul(det(Mat4x4 { row0: b0, row1: b3, row2: ab.row2, row3: ab.row3 })),
    );
    lemma_sum4_kill_first(e0, e1, e2, e3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        e0.add(e1).add(e2).add(e3), e1.add(e2).add(e3));

    // Branch results
    lemma_col0_branch1(a, b);
    lemma_col0_branch2(a, b);
    lemma_col0_branch3(a, b);

    // Scale each: a1.i * det(...) ≡ a1.i * (cx.j * db) ≡ (a1.i * cx.j) * db
    ring_lemmas::lemma_mul_congruence_right(a1.y,
        det(Mat4x4 { row0: b0, row1: b1, row2: ab.row2, row3: ab.row3 }),
        cx.x.mul(db));
    T::axiom_mul_associative(a1.y, cx.x, db);
    T::axiom_eqv_symmetric(a1.y.mul(cx.x).mul(db), a1.y.mul(cx.x.mul(db)));
    T::axiom_eqv_transitive(e1, a1.y.mul(cx.x.mul(db)), a1.y.mul(cx.x).mul(db));

    ring_lemmas::lemma_mul_congruence_right(a1.z,
        det(Mat4x4 { row0: b0, row1: b2, row2: ab.row2, row3: ab.row3 }),
        cx.y.mul(db));
    T::axiom_mul_associative(a1.z, cx.y, db);
    T::axiom_eqv_symmetric(a1.z.mul(cx.y).mul(db), a1.z.mul(cx.y.mul(db)));
    T::axiom_eqv_transitive(e2, a1.z.mul(cx.y.mul(db)), a1.z.mul(cx.y).mul(db));

    ring_lemmas::lemma_mul_congruence_right(a1.w,
        det(Mat4x4 { row0: b0, row1: b3, row2: ab.row2, row3: ab.row3 }),
        cx.z.mul(db));
    T::axiom_mul_associative(a1.w, cx.z, db);
    T::axiom_eqv_symmetric(a1.w.mul(cx.z).mul(db), a1.w.mul(cx.z.mul(db)));
    T::axiom_eqv_transitive(e3, a1.w.mul(cx.z.mul(db)), a1.w.mul(cx.z).mul(db));

    // 3-sum congruence
    lemma_add_congruence_3(
        e1, a1.y.mul(cx.x).mul(db),
        e2, a1.z.mul(cx.y).mul(db),
        e3, a1.w.mul(cx.z).mul(db));

    // Factor out db
    lemma_factor_3(a1.y.mul(cx.x), a1.z.mul(cx.y), a1.w.mul(cx.z), db);

    // Chain: det ≡ 3-sum ≡ factored ≡ cofactor_vec.x * db
    let sum_factored = a1.y.mul(cx.x).mul(db)
        .add(a1.z.mul(cx.y).mul(db))
        .add(a1.w.mul(cx.z).mul(db));

    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        e1.add(e2).add(e3), sum_factored);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        sum_factored, cofactor_vec(a1, a.row2, a.row3).x.mul(db));
}

} // verus!
