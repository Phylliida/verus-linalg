use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use crate::vec3::Vec3;
use crate::vec3::ops::cross;
use crate::vec4::Vec4;
use crate::vec4::ops::{scale, dot};
use super::Mat4x4;
use super::ops::{det, mat_mul, cofactor_vec, drop_x, drop_y, drop_z, drop_w,
    lemma_det_linear_first_row, lemma_det_linear_second_row, lemma_det_linear_third_row, lemma_det_linear_fourth_row,
    lemma_det_scale_first_row, lemma_det_scale_second_row, lemma_det_scale_third_row, lemma_det_scale_fourth_row,
    lemma_det_zero_repeated_row_12, lemma_det_zero_repeated_row_13, lemma_det_zero_repeated_row_23,
    lemma_det_swap_rows_12, lemma_det_swap_rows_13, lemma_det_swap_rows_23,
    lemma_factor_4, lemma_add_congruence_4,
    lemma_det_as_dot,
};
use super::det_advanced::{
    lemma_det_zero_repeated_row_01, lemma_det_zero_repeated_row_02, lemma_det_zero_repeated_row_03,
    lemma_det_swap_rows_01, lemma_det_swap_rows_02, lemma_det_swap_rows_03,
};
use crate::mat3::ops::{lemma_mul_zero_by_eqv, lemma_add_congruence_3, lemma_factor_3};

verus! {

//  ===========================================================================
//  Section 1: Sum4 kill helpers
//  Kill zero terms from left-associated 4-term sums: ((a+b)+c)+d
//  ===========================================================================

///  Kill first: a≡0 → ((a+b)+c)+d ≡ (b+c)+d
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

///  Kill first and second: a≡0, b≡0 → ((a+b)+c)+d ≡ c+d
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

///  Kill first and third: a≡0, c≡0 → ((a+b)+c)+d ≡ b+d
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

///  Kill first and fourth: a≡0, d≡0 → ((a+b)+c)+d ≡ b+c
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

///  Kill first, second, third: a≡0, b≡0, c≡0 → ((a+b)+c)+d ≡ d
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

///  Kill first, second, fourth: a≡0, b≡0, d≡0 → ((a+b)+c)+d ≡ c
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

///  Kill first, third, fourth: a≡0, c≡0, d≡0 → ((a+b)+c)+d ≡ b
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

///  Kill second: b≡0 → ((a+b)+c)+d ≡ (a+c)+d
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

///  Kill second and third: b≡0, c≡0 → ((a+b)+c)+d ≡ a+d
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

///  Kill second and fourth: b≡0, d≡0 → ((a+b)+c)+d ≡ a+c
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

///  Kill second, third, fourth: b≡0, c≡0, d≡0 → ((a+b)+c)+d ≡ a
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

///  Kill third: c≡0 → ((a+b)+c)+d ≡ (a+b)+d
pub proof fn lemma_sum4_kill_third<T: Ring>(a: T, b: T, c: T, d: T)
    requires c.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(a.add(b).add(d)),
{
    additive_group_lemmas::lemma_add_congruence_right(a.add(b), c, T::zero());
    T::axiom_add_zero_right(a.add(b));
    T::axiom_eqv_transitive(a.add(b).add(c), a.add(b).add(T::zero()), a.add(b));
    T::axiom_add_congruence_left(a.add(b).add(c), a.add(b), d);
}

///  Kill third and fourth: c≡0, d≡0 → ((a+b)+c)+d ≡ a+b
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

///  Kill fourth: d≡0 → ((a+b)+c)+d ≡ (a+b)+c
pub proof fn lemma_sum4_kill_fourth<T: Ring>(a: T, b: T, c: T, d: T)
    requires d.eqv(T::zero()),
    ensures a.add(b).add(c).add(d).eqv(a.add(b).add(c)),
{
    additive_group_lemmas::lemma_add_congruence_right(a.add(b).add(c), d, T::zero());
    T::axiom_add_zero_right(a.add(b).add(c));
    T::axiom_eqv_transitive(a.add(b).add(c).add(d), a.add(b).add(c).add(T::zero()), a.add(b).add(c));
}

//  ===========================================================================
//  Section 2: Row expansion helpers
//  Expand a 4-term scaled Vec4 sum in a specific row of det into 4 scaled dets
//  ===========================================================================

///  Expand det when row 1 (second row) is a 4-term scaled sum.
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

    //  Linearity: split 3 times
    lemma_det_linear_second_row(r0, x.add(y).add(z), w, r2, r3);
    lemma_det_linear_second_row(r0, x.add(y), z, r2, r3);
    lemma_det_linear_second_row(r0, x, y, r2, r3);

    //  Scale: pull out scalars
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

    //  Chain inner pair: dx + dy ≡ s0*d0 + s1*d1
    T::axiom_add_congruence_left(dx, s0.mul(d0), dy);
    additive_group_lemmas::lemma_add_congruence_right(s0.mul(d0), dy, s1.mul(d1));
    T::axiom_eqv_transitive(dx.add(dy), s0.mul(d0).add(dy), s0.mul(d0).add(s1.mul(d1)));

    //  det(r0, x+y, ...) ≡ dx+dy ≡ s0*d0 + s1*d1
    let dxy = det(Mat4x4 { row0: r0, row1: x.add(y), row2: r2, row3: r3 });
    T::axiom_eqv_transitive(dxy, dx.add(dy), s0.mul(d0).add(s1.mul(d1)));

    //  dxy + dz ≡ (s0*d0+s1*d1) + s2*d2
    T::axiom_add_congruence_left(dxy, s0.mul(d0).add(s1.mul(d1)), dz);
    additive_group_lemmas::lemma_add_congruence_right(
        s0.mul(d0).add(s1.mul(d1)), dz, s2.mul(d2));
    T::axiom_eqv_transitive(dxy.add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)));

    //  det(r0, (x+y)+z, ...) ≡ (s0*d0+s1*d1)+s2*d2
    let dxyz = det(Mat4x4 { row0: r0, row1: x.add(y).add(z), row2: r2, row3: r3 });
    T::axiom_eqv_transitive(dxyz, dxy.add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)));

    //  dxyz + dw ≡ ((s0*d0+s1*d1)+s2*d2) + s3*d3
    T::axiom_add_congruence_left(dxyz,
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)), dw);
    additive_group_lemmas::lemma_add_congruence_right(
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)), dw, s3.mul(d3));
    T::axiom_eqv_transitive(dxyz.add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(s3.mul(d3)));

    //  det(r0, ((x+y)+z)+w, ...) ≡ final 4-term sum
    let dxyzw = det(Mat4x4 { row0: r0, row1: x.add(y).add(z).add(w), row2: r2, row3: r3 });
    T::axiom_eqv_transitive(dxyzw, dxyz.add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(s3.mul(d3)));
}

///  Expand det when row 2 (third row) is a 4-term scaled sum.
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

///  Expand det when row 3 (fourth row) is a 4-term scaled sum.
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

//  ===========================================================================
//  Section 3: Col0 branch helpers
//  Each proves det(b0, b_j, ABr2, ABr3) ≡ cross(dx(a2),dx(a3)).component * db
//  ===========================================================================

///  Branch 1: det(b0, b1, ABr2, ABr3) ≡ cross(drop_x(a2), drop_x(a3)).x * det(b)
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

    //  ---- Expand row 2 (ABr2) ----
    lemma_det_expand_third_row_4(b0, b1,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    //  Kill terms 0,1 (repeated rows 02, 12)
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

    //  ---- Sub-branch 1a: det(b0,b1,b2,ABr3) ≡ a3.w * db ----
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

    //  t2 = a2.z * det(...) ≡ a2.z * (a3.w * db) ≡ (a2.z * a3.w) * db
    ring_lemmas::lemma_mul_congruence_right(a2.z,
        det(Mat4x4 { row0: b0, row1: b1, row2: b2, row3: ab.row3 }),
        a3.w.mul(db));
    T::axiom_mul_associative(a2.z, a3.w, db);
    T::axiom_eqv_symmetric(a2.z.mul(a3.w).mul(db), a2.z.mul(a3.w.mul(db)));
    T::axiom_eqv_transitive(t2, a2.z.mul(a3.w.mul(db)), a2.z.mul(a3.w).mul(db));

    //  ---- Sub-branch 1b: det(b0,b1,b3,ABr3) ≡ a3.z * (-db) ----
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

    //  det(b0,b1,b3,b2) ≡ -db by swap_23
    lemma_det_swap_rows_23(b);
    //  Chain: a3.z * det(b0,b1,b3,b2) ≡ a3.z * (-db) ≡ -(a3.z * db)
    ring_lemmas::lemma_mul_congruence_right(a3.z,
        det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 }), db.neg());
    ring_lemmas::lemma_mul_neg_right(a3.z, db);
    T::axiom_eqv_transitive(
        a3.z.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 })),
        a3.z.mul(db.neg()), a3.z.mul(db).neg());
    //  det(b0,b1,b3,ABr3) ≡ -(a3.z*db)
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: ab.row3 }),
        a3.z.mul(det(Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 })),
        a3.z.mul(db).neg());

    //  t3 = a2.w * det(...) ≡ a2.w * (-(a3.z*db)) ≡ -((a2.w*a3.z)*db)
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

    //  ---- Combine: t2 + t3 ≡ (p-q)*db = cross(dx(a2),dx(a3)).x * db ----
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

    //  Final chain
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b1, row2: ab.row2, row3: ab.row3 }),
        t2.add(t3),
        cross(drop_x(a2), drop_x(a3)).x.mul(db));
}

///  Branch 2: det(b0, b2, ABr2, ABr3) ≡ cross(drop_x(a2), drop_x(a3)).y * det(b)
///  Note: negative term comes first, needs additive commutative step.
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

    //  ---- Expand row 2 (ABr2) ----
    lemma_det_expand_third_row_4(b0, b2,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    //  Kill terms 0,2 (repeated rows 02, 12)
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

    //  ---- Sub-branch 2a: det(b0,b2,b1,ABr3) ≡ a3.w * (-db) ----
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

    //  det(b0,b2,b1,b3) ≡ -db by swap_12
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

    //  t1 = a2.y * det(...) ≡ a2.y * (-(a3.w*db)) ≡ -((a2.y*a3.w)*db)
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

    //  ---- Sub-branch 2b: det(b0,b2,b3,ABr3) ≡ a3.y * db ----
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

    //  det(b0,b2,b3,b1) ≡ db by double swap: swap_12 then swap_23
    let m_swap = Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b3 };
    //  swap_12(b) already called above: det(m_swap) ≡ db.neg()
    lemma_det_swap_rows_23(m_swap);
    //  det(b0,b2,b3,b1) ≡ det(m_swap).neg()
    additive_group_lemmas::lemma_neg_congruence(det(m_swap), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m_swap).neg(), db.neg().neg(), db);
    let d_2b = det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: b1 });
    T::axiom_eqv_transitive(d_2b, det(m_swap).neg(), db);

    //  det(b0,b2,b3,ABr3) ≡ a3.y * db
    ring_lemmas::lemma_mul_congruence_right(a3.y, d_2b, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: ab.row3 }),
        a3.y.mul(d_2b), a3.y.mul(db));

    //  t3 = a2.w * det(...) ≡ a2.w * (a3.y * db) ≡ (a2.w * a3.y) * db
    ring_lemmas::lemma_mul_congruence_right(a2.w,
        det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: ab.row3 }),
        a3.y.mul(db));
    T::axiom_mul_associative(a2.w, a3.y, db);
    T::axiom_eqv_symmetric(a2.w.mul(a3.y).mul(db), a2.w.mul(a3.y.mul(db)));
    T::axiom_eqv_transitive(t3, a2.w.mul(a3.y.mul(db)), a2.w.mul(a3.y).mul(db));

    //  ---- Combine: t1 + t3, negative first → commute ----
    T::axiom_add_congruence_left(t1, a2.y.mul(a3.w).mul(db).neg(), t3);
    additive_group_lemmas::lemma_add_congruence_right(
        a2.y.mul(a3.w).mul(db).neg(), t3, a2.w.mul(a3.y).mul(db));
    T::axiom_eqv_transitive(t1.add(t3),
        a2.y.mul(a3.w).mul(db).neg().add(t3),
        a2.y.mul(a3.w).mul(db).neg().add(a2.w.mul(a3.y).mul(db)));

    //  Commute: -(q*db) + p*db → p*db + (-(q*db))
    let p = a2.w.mul(a3.y);
    let q = a2.y.mul(a3.w);
    T::axiom_add_commutative(q.mul(db).neg(), p.mul(db));
    T::axiom_eqv_transitive(t1.add(t3),
        q.mul(db).neg().add(p.mul(db)),
        p.mul(db).add(q.mul(db).neg()));

    //  Factor: p*db + (-(q*db)) ≡ (p-q)*db
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

    //  Final chain
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b2, row2: ab.row2, row3: ab.row3 }),
        t1.add(t3),
        cross(drop_x(a2), drop_x(a3)).y.mul(db));
}

///  Branch 3: det(b0, b3, ABr2, ABr3) ≡ cross(drop_x(a2), drop_x(a3)).z * det(b)
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

    //  ---- Expand row 2 (ABr2) ----
    lemma_det_expand_third_row_4(b0, b3,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    //  Kill terms 0,3 (repeated rows 02, 12)
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

    //  ---- Sub-branch 3a: det(b0,b3,b1,ABr3) ≡ a3.z * db ----
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

    //  det(b0,b3,b1,b2) ≡ db by double swap: swap_23 then swap_12
    lemma_det_swap_rows_23(b);
    let m_swap = Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 };
    //  det(m_swap) ≡ db.neg()
    lemma_det_swap_rows_12(m_swap);
    //  det(b0,b3,b1,b2) ≡ det(m_swap).neg()
    additive_group_lemmas::lemma_neg_congruence(det(m_swap), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m_swap).neg(), db.neg().neg(), db);
    let d_3a = det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: b2 });
    T::axiom_eqv_transitive(d_3a, det(m_swap).neg(), db);

    //  det(b0,b3,b1,ABr3) ≡ a3.z * db
    ring_lemmas::lemma_mul_congruence_right(a3.z, d_3a, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: ab.row3 }),
        a3.z.mul(d_3a), a3.z.mul(db));

    //  t1 = a2.y * det(...) ≡ a2.y * (a3.z * db) ≡ (a2.y * a3.z) * db
    ring_lemmas::lemma_mul_congruence_right(a2.y,
        det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: ab.row3 }),
        a3.z.mul(db));
    T::axiom_mul_associative(a2.y, a3.z, db);
    T::axiom_eqv_symmetric(a2.y.mul(a3.z).mul(db), a2.y.mul(a3.z.mul(db)));
    T::axiom_eqv_transitive(t1, a2.y.mul(a3.z.mul(db)), a2.y.mul(a3.z).mul(db));

    //  ---- Sub-branch 3b: det(b0,b3,b2,ABr3) ≡ a3.y * (-db) ----
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

    //  det(b0,b3,b2,b1) ≡ -db by swap_13
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

    //  t2 = a2.z * det(...) ≡ a2.z * (-(a3.y*db)) ≡ -((a2.z*a3.y)*db)
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

    //  ---- Combine: t1 + t2 ≡ (p-q)*db = cross(dx(a2),dx(a3)).z * db ----
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

    //  Final chain
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b0, row1: b3, row2: ab.row2, row3: ab.row3 }),
        t1.add(t2),
        cross(drop_x(a2), drop_x(a3)).z.mul(db));
}

//  ===========================================================================
//  Section 4: Col0 main
//  det(b0, ABr1, ABr2, ABr3) ≡ cofactor_vec(a1,a2,a3).x * det(b)
//  ===========================================================================

///  Column 0 of det multiplicative:
///  det(b0, ABr1, ABr2, ABr3) ≡ cofactor_vec(a1, a2, a3).x * det(b)
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

    //  Expand row 1 (ABr1) → 4 terms
    lemma_det_expand_second_row_4(b0,
        a1.x, b0, a1.y, b1, a1.z, b2, a1.w, b3, ab.row2, ab.row3);

    //  Kill first (repeated rows 01)
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

    //  Branch results
    lemma_col0_branch1(a, b);
    lemma_col0_branch2(a, b);
    lemma_col0_branch3(a, b);

    //  Scale each: a1.i * det(...) ≡ a1.i * (cx.j * db) ≡ (a1.i * cx.j) * db
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

    //  3-sum congruence
    lemma_add_congruence_3(
        e1, a1.y.mul(cx.x).mul(db),
        e2, a1.z.mul(cx.y).mul(db),
        e3, a1.w.mul(cx.z).mul(db));

    //  Factor out db
    lemma_factor_3(a1.y.mul(cx.x), a1.z.mul(cx.y), a1.w.mul(cx.z), db);

    //  Chain: det ≡ 3-sum ≡ factored ≡ cofactor_vec.x * db
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

//  ===========================================================================
//  Helper: (a - b).neg() ≡ b - a
//  ===========================================================================

proof fn lemma_neg_sub<T: Ring>(a: T, b: T)
    ensures a.sub(b).neg().eqv(b.sub(a)),
{
    T::axiom_sub_is_add_neg(a, b);
    additive_group_lemmas::lemma_neg_congruence(a.sub(b), a.add(b.neg()));
    additive_group_lemmas::lemma_neg_add(a, b.neg());
    T::axiom_eqv_transitive(a.sub(b).neg(), a.add(b.neg()).neg(), a.neg().add(b.neg().neg()));
    additive_group_lemmas::lemma_neg_involution(b);
    additive_group_lemmas::lemma_add_congruence_right(a.neg(), b.neg().neg(), b);
    T::axiom_eqv_transitive(a.sub(b).neg(), a.neg().add(b.neg().neg()), a.neg().add(b));
    T::axiom_add_commutative(a.neg(), b);
    T::axiom_eqv_transitive(a.sub(b).neg(), a.neg().add(b), b.add(a.neg()));
    T::axiom_sub_is_add_neg(b, a);
    T::axiom_eqv_symmetric(b.sub(a), b.add(a.neg()));
    T::axiom_eqv_transitive(a.sub(b).neg(), b.add(a.neg()), b.sub(a));
}

//  ===========================================================================
//  Section 5: Col1 branch helpers
//  Each proves det(b1, b_j, ABr2, ABr3) ≡ -cross(drop_y(a2),drop_y(a3)).component * db
//  ===========================================================================

///  Branch 1 (col1): det(b1, b0, ABr2, ABr3) ≡ cross(drop_y(a2),drop_y(a3)).x.mul(db).neg()
proof fn lemma_col1_branch1<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row1, row1: b.row0,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cross(drop_y(a.row2), drop_y(a.row3)).x.mul(det(b)).neg()),
{
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let a2 = a.row2;
    let a3 = a.row3;
    let ab = mat_mul(a, b);
    let db = det(b);

    //  ---- Expand row 2 (ABr2) ----
    lemma_det_expand_third_row_4(b1, b0,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    //  Kill terms 0 (row12: b0=b0), 1 (row02: b1=b1)
    lemma_det_zero_repeated_row_12(b1, b0, ab.row3);
    lemma_det_zero_repeated_row_02(b1, b0, ab.row3);
    lemma_mul_zero_by_eqv(a2.x,
        det(Mat4x4 { row0: b1, row1: b0, row2: b0, row3: ab.row3 }));
    lemma_mul_zero_by_eqv(a2.y,
        det(Mat4x4 { row0: b1, row1: b0, row2: b1, row3: ab.row3 }));

    let (t0, t1, t2, t3) = (
        a2.x.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b0, row3: ab.row3 })),
        a2.y.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b1, row3: ab.row3 })),
        a2.z.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: ab.row3 })),
        a2.w.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b3, row3: ab.row3 })),
    );
    lemma_sum4_kill_first_second(t0, t1, t2, t3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b0, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1).add(t2).add(t3), t2.add(t3));

    //  ---- Sub-branch 1a: det(b1,b0,b2,ABr3) → a3.w * (-db) ----
    lemma_det_expand_fourth_row_4(b1, b0, b2,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_13(b1, b0, b2);
    lemma_det_zero_repeated_row_03(b1, b0, b2);
    lemma_det_zero_repeated_row_23(b1, b0, b2);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: b2 }));
    let (u0, u1, u2, u3) = (
        a3.x.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: b3 })),
    );
    lemma_sum4_kill_first_second_third(u0, u1, u2, u3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: ab.row3 }),
        u0.add(u1).add(u2).add(u3),
        a3.w.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: b3 })));

    //  det(b1,b0,b2,b3) ≡ -db by swap_01
    lemma_det_swap_rows_01(b);
    ring_lemmas::lemma_mul_congruence_right(a3.w,
        det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: b3 }), db.neg());
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: ab.row3 }),
        a3.w.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: b3 })),
        a3.w.mul(db.neg()));
    ring_lemmas::lemma_mul_neg_right(a3.w, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: ab.row3 }),
        a3.w.mul(db.neg()), a3.w.mul(db).neg());

    //  t2 ≡ a2.z * (-(a3.w*db)) ≡ -((a2.z*a3.w)*db)
    ring_lemmas::lemma_mul_congruence_right(a2.z,
        det(Mat4x4 { row0: b1, row1: b0, row2: b2, row3: ab.row3 }),
        a3.w.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a2.z, a3.w.mul(db));
    T::axiom_eqv_transitive(t2, a2.z.mul(a3.w.mul(db).neg()), a2.z.mul(a3.w.mul(db)).neg());
    T::axiom_mul_associative(a2.z, a3.w, db);
    T::axiom_eqv_symmetric(a2.z.mul(a3.w).mul(db), a2.z.mul(a3.w.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a2.z.mul(a3.w.mul(db)), a2.z.mul(a3.w).mul(db));
    T::axiom_eqv_transitive(t2, a2.z.mul(a3.w.mul(db)).neg(), a2.z.mul(a3.w).mul(db).neg());

    //  ---- Sub-branch 1b: det(b1,b0,b3,ABr3) → a3.z * db ----
    lemma_det_expand_fourth_row_4(b1, b0, b3,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_13(b1, b0, b3);
    lemma_det_zero_repeated_row_03(b1, b0, b3);
    lemma_det_zero_repeated_row_23(b1, b0, b3);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b1, row1: b0, row2: b3, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b1, row1: b0, row2: b3, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b1, row1: b0, row2: b3, row3: b3 }));
    let (v0, v1, v2, v3) = (
        a3.x.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b3, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b3, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b3, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b3, row3: b3 })),
    );
    lemma_sum4_kill_first_second_fourth(v0, v1, v2, v3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b0, row2: b3, row3: ab.row3 }),
        v0.add(v1).add(v2).add(v3),
        a3.z.mul(det(Mat4x4 { row0: b1, row1: b0, row2: b3, row3: b2 })));

    //  det(b1,b0,b3,b2) ≡ db by double swap: swap_23 on m={b1,b0,b2,b3}
    let m_swap = Mat4x4 { row0: b1, row1: b0, row2: b2, row3: b3 };
    lemma_det_swap_rows_23(m_swap);
    additive_group_lemmas::lemma_neg_congruence(det(m_swap), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m_swap).neg(), db.neg().neg(), db);
    let d_1b = det(Mat4x4 { row0: b1, row1: b0, row2: b3, row3: b2 });
    T::axiom_eqv_transitive(d_1b, det(m_swap).neg(), db);

    ring_lemmas::lemma_mul_congruence_right(a3.z, d_1b, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b0, row2: b3, row3: ab.row3 }),
        a3.z.mul(d_1b), a3.z.mul(db));

    //  t3 ≡ a2.w * (a3.z * db) ≡ (a2.w*a3.z)*db
    ring_lemmas::lemma_mul_congruence_right(a2.w,
        det(Mat4x4 { row0: b1, row1: b0, row2: b3, row3: ab.row3 }),
        a3.z.mul(db));
    T::axiom_mul_associative(a2.w, a3.z, db);
    T::axiom_eqv_symmetric(a2.w.mul(a3.z).mul(db), a2.w.mul(a3.z.mul(db)));
    T::axiom_eqv_transitive(t3, a2.w.mul(a3.z.mul(db)), a2.w.mul(a3.z).mul(db));

    //  ---- Combine: t2+t3, negative first → commute then factor ----
    T::axiom_add_congruence_left(t2, a2.z.mul(a3.w).mul(db).neg(), t3);
    additive_group_lemmas::lemma_add_congruence_right(
        a2.z.mul(a3.w).mul(db).neg(), t3, a2.w.mul(a3.z).mul(db));
    T::axiom_eqv_transitive(t2.add(t3),
        a2.z.mul(a3.w).mul(db).neg().add(t3),
        a2.z.mul(a3.w).mul(db).neg().add(a2.w.mul(a3.z).mul(db)));

    let p = a2.w.mul(a3.z);
    let q = a2.z.mul(a3.w);
    T::axiom_add_commutative(q.mul(db).neg(), p.mul(db));
    T::axiom_eqv_transitive(t2.add(t3),
        q.mul(db).neg().add(p.mul(db)),
        p.mul(db).add(q.mul(db).neg()));

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
        p.sub(q).mul(db));

    //  p.sub(q) ≡ cross.x.neg() via neg_sub
    let cx = cross(drop_y(a2), drop_y(a3));
    lemma_neg_sub(q, p);
    //  q.sub(p).neg() ≡ p.sub(q), and q.sub(p) = cx.x definitionally
    T::axiom_eqv_symmetric(q.sub(p).neg(), p.sub(q));
    //  So p.sub(q) ≡ q.sub(p).neg() = cx.x.neg()
    T::axiom_mul_congruence_left(p.sub(q), cx.x.neg(), db);
    T::axiom_eqv_transitive(t2.add(t3), p.sub(q).mul(db), cx.x.neg().mul(db));
    ring_lemmas::lemma_mul_neg_left(cx.x, db);
    T::axiom_eqv_transitive(t2.add(t3), cx.x.neg().mul(db), cx.x.mul(db).neg());

    //  Final chain
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b0, row2: ab.row2, row3: ab.row3 }),
        t2.add(t3), cx.x.mul(db).neg());
}

///  Branch 2 (col1): det(b1, b2, ABr2, ABr3) ≡ cross(drop_y(a2),drop_y(a3)).y.mul(db).neg()
proof fn lemma_col1_branch2<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row1, row1: b.row2,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cross(drop_y(a.row2), drop_y(a.row3)).y.mul(det(b)).neg()),
{
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let a2 = a.row2;
    let a3 = a.row3;
    let ab = mat_mul(a, b);
    let db = det(b);

    //  ---- Expand row 2 (ABr2) ----
    lemma_det_expand_third_row_4(b1, b2,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    //  Kill terms 1 (row02: b1=b1), 2 (row12: b2=b2)
    lemma_det_zero_repeated_row_02(b1, b2, ab.row3);
    lemma_det_zero_repeated_row_12(b1, b2, ab.row3);
    lemma_mul_zero_by_eqv(a2.y,
        det(Mat4x4 { row0: b1, row1: b2, row2: b1, row3: ab.row3 }));
    lemma_mul_zero_by_eqv(a2.z,
        det(Mat4x4 { row0: b1, row1: b2, row2: b2, row3: ab.row3 }));

    let (t0, t1, t2, t3) = (
        a2.x.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b0, row3: ab.row3 })),
        a2.y.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b1, row3: ab.row3 })),
        a2.z.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b2, row3: ab.row3 })),
        a2.w.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b3, row3: ab.row3 })),
    );
    lemma_sum4_kill_second_third(t0, t1, t2, t3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b2, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1).add(t2).add(t3), t0.add(t3));

    //  ---- Sub-branch 2a: det(b1,b2,b0,ABr3) → a3.w * db ----
    lemma_det_expand_fourth_row_4(b1, b2, b0,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_23(b1, b2, b0);
    lemma_det_zero_repeated_row_03(b1, b2, b0);
    lemma_det_zero_repeated_row_13(b1, b2, b0);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b1, row1: b2, row2: b0, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b1, row1: b2, row2: b0, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b1, row1: b2, row2: b0, row3: b2 }));
    let (u0, u1, u2, u3) = (
        a3.x.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b0, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b0, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b0, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b0, row3: b3 })),
    );
    lemma_sum4_kill_first_second_third(u0, u1, u2, u3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b2, row2: b0, row3: ab.row3 }),
        u0.add(u1).add(u2).add(u3),
        a3.w.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b0, row3: b3 })));

    //  det(b1,b2,b0,b3) ≡ db by double swap: swap_01 then swap_12
    lemma_det_swap_rows_01(b);
    let m1 = Mat4x4 { row0: b1, row1: b0, row2: b2, row3: b3 };
    lemma_det_swap_rows_12(m1);
    additive_group_lemmas::lemma_neg_congruence(det(m1), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m1).neg(), db.neg().neg(), db);
    let d_2a = det(Mat4x4 { row0: b1, row1: b2, row2: b0, row3: b3 });
    T::axiom_eqv_transitive(d_2a, det(m1).neg(), db);

    ring_lemmas::lemma_mul_congruence_right(a3.w, d_2a, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b2, row2: b0, row3: ab.row3 }),
        a3.w.mul(d_2a), a3.w.mul(db));

    //  t0 ≡ a2.x * (a3.w * db) ≡ (a2.x*a3.w)*db
    ring_lemmas::lemma_mul_congruence_right(a2.x,
        det(Mat4x4 { row0: b1, row1: b2, row2: b0, row3: ab.row3 }),
        a3.w.mul(db));
    T::axiom_mul_associative(a2.x, a3.w, db);
    T::axiom_eqv_symmetric(a2.x.mul(a3.w).mul(db), a2.x.mul(a3.w.mul(db)));
    T::axiom_eqv_transitive(t0, a2.x.mul(a3.w.mul(db)), a2.x.mul(a3.w).mul(db));

    //  ---- Sub-branch 2b: det(b1,b2,b3,ABr3) → a3.x * (-db) ----
    lemma_det_expand_fourth_row_4(b1, b2, b3,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_03(b1, b2, b3);
    lemma_det_zero_repeated_row_13(b1, b2, b3);
    lemma_det_zero_repeated_row_23(b1, b2, b3);
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b1, row1: b2, row2: b3, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b1, row1: b2, row2: b3, row3: b2 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b1, row1: b2, row2: b3, row3: b3 }));
    let (w0, w1, w2, w3) = (
        a3.x.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b3, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b3, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b3, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b3, row3: b3 })),
    );
    lemma_sum4_kill_second_third_fourth(w0, w1, w2, w3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b2, row2: b3, row3: ab.row3 }),
        w0.add(w1).add(w2).add(w3),
        a3.x.mul(det(Mat4x4 { row0: b1, row1: b2, row2: b3, row3: b0 })));

    //  det(b1,b2,b3,b0) ≡ -db by triple swap: swap_23 on m2={b1,b2,b0,b3}
    let m2 = Mat4x4 { row0: b1, row1: b2, row2: b0, row3: b3 };
    lemma_det_swap_rows_23(m2);
    additive_group_lemmas::lemma_neg_congruence(det(m2), db);
    let d_2b = det(Mat4x4 { row0: b1, row1: b2, row2: b3, row3: b0 });
    T::axiom_eqv_transitive(d_2b, det(m2).neg(), db.neg());

    ring_lemmas::lemma_mul_congruence_right(a3.x, d_2b, db.neg());
    ring_lemmas::lemma_mul_neg_right(a3.x, db);
    T::axiom_eqv_transitive(
        a3.x.mul(d_2b), a3.x.mul(db.neg()), a3.x.mul(db).neg());
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b2, row2: b3, row3: ab.row3 }),
        a3.x.mul(d_2b), a3.x.mul(db).neg());

    //  t3 ≡ a2.w * (-(a3.x*db)) ≡ -((a2.w*a3.x)*db)
    ring_lemmas::lemma_mul_congruence_right(a2.w,
        det(Mat4x4 { row0: b1, row1: b2, row2: b3, row3: ab.row3 }),
        a3.x.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a2.w, a3.x.mul(db));
    T::axiom_eqv_transitive(t3, a2.w.mul(a3.x.mul(db).neg()), a2.w.mul(a3.x.mul(db)).neg());
    T::axiom_mul_associative(a2.w, a3.x, db);
    T::axiom_eqv_symmetric(a2.w.mul(a3.x).mul(db), a2.w.mul(a3.x.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a2.w.mul(a3.x.mul(db)), a2.w.mul(a3.x).mul(db));
    T::axiom_eqv_transitive(t3, a2.w.mul(a3.x.mul(db)).neg(), a2.w.mul(a3.x).mul(db).neg());

    //  ---- Combine: t0+t3, positive first ----
    T::axiom_add_congruence_left(t0, a2.x.mul(a3.w).mul(db), t3);
    additive_group_lemmas::lemma_add_congruence_right(
        a2.x.mul(a3.w).mul(db), t3, a2.w.mul(a3.x).mul(db).neg());
    T::axiom_eqv_transitive(t0.add(t3),
        a2.x.mul(a3.w).mul(db).add(t3),
        a2.x.mul(a3.w).mul(db).add(a2.w.mul(a3.x).mul(db).neg()));

    let p = a2.x.mul(a3.w);
    let q = a2.w.mul(a3.x);
    T::axiom_sub_is_add_neg(p.mul(db), q.mul(db));
    T::axiom_eqv_symmetric(
        p.mul(db).sub(q.mul(db)), p.mul(db).add(q.mul(db).neg()));
    ring_lemmas::lemma_sub_mul_right(p, q, db);
    T::axiom_eqv_symmetric(p.sub(q).mul(db), p.mul(db).sub(q.mul(db)));
    T::axiom_eqv_transitive(
        p.mul(db).add(q.mul(db).neg()),
        p.mul(db).sub(q.mul(db)),
        p.sub(q).mul(db));
    T::axiom_eqv_transitive(t0.add(t3),
        p.mul(db).add(q.mul(db).neg()),
        p.sub(q).mul(db));

    //  p.sub(q) ≡ cross.y.neg() via neg_sub
    let cx = cross(drop_y(a2), drop_y(a3));
    lemma_neg_sub(q, p);
    T::axiom_eqv_symmetric(q.sub(p).neg(), p.sub(q));
    T::axiom_mul_congruence_left(p.sub(q), cx.y.neg(), db);
    T::axiom_eqv_transitive(t0.add(t3), p.sub(q).mul(db), cx.y.neg().mul(db));
    ring_lemmas::lemma_mul_neg_left(cx.y, db);
    T::axiom_eqv_transitive(t0.add(t3), cx.y.neg().mul(db), cx.y.mul(db).neg());

    //  Final chain
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b2, row2: ab.row2, row3: ab.row3 }),
        t0.add(t3), cx.y.mul(db).neg());
}

///  Branch 3 (col1): det(b1, b3, ABr2, ABr3) ≡ cross(drop_y(a2),drop_y(a3)).z.mul(db).neg()
proof fn lemma_col1_branch3<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row1, row1: b.row3,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cross(drop_y(a.row2), drop_y(a.row3)).z.mul(det(b)).neg()),
{
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let a2 = a.row2;
    let a3 = a.row3;
    let ab = mat_mul(a, b);
    let db = det(b);

    //  ---- Expand row 2 (ABr2) ----
    lemma_det_expand_third_row_4(b1, b3,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    //  Kill terms 1 (row02: b1=b1), 3 (row12: b3=b3)
    lemma_det_zero_repeated_row_02(b1, b3, ab.row3);
    lemma_det_zero_repeated_row_12(b1, b3, ab.row3);
    lemma_mul_zero_by_eqv(a2.y,
        det(Mat4x4 { row0: b1, row1: b3, row2: b1, row3: ab.row3 }));
    lemma_mul_zero_by_eqv(a2.w,
        det(Mat4x4 { row0: b1, row1: b3, row2: b3, row3: ab.row3 }));

    let (t0, t1, t2, t3) = (
        a2.x.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b0, row3: ab.row3 })),
        a2.y.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b1, row3: ab.row3 })),
        a2.z.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b2, row3: ab.row3 })),
        a2.w.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b3, row3: ab.row3 })),
    );
    lemma_sum4_kill_second_fourth(t0, t1, t2, t3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b3, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1).add(t2).add(t3), t0.add(t2));

    //  ---- Sub-branch 3a: det(b1,b3,b0,ABr3) → a3.z * (-db) ----
    lemma_det_expand_fourth_row_4(b1, b3, b0,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_23(b1, b3, b0);
    lemma_det_zero_repeated_row_03(b1, b3, b0);
    lemma_det_zero_repeated_row_13(b1, b3, b0);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b1, row1: b3, row2: b0, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b1, row1: b3, row2: b0, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b1, row1: b3, row2: b0, row3: b3 }));
    let (u0, u1, u2, u3) = (
        a3.x.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b0, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b0, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b0, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b0, row3: b3 })),
    );
    lemma_sum4_kill_first_second_fourth(u0, u1, u2, u3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b3, row2: b0, row3: ab.row3 }),
        u0.add(u1).add(u2).add(u3),
        a3.z.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b0, row3: b2 })));

    //  det(b1,b3,b0,b2) ≡ -db by triple swap: swap_01, swap_13, swap_23
    lemma_det_swap_rows_01(b);
    let m1 = Mat4x4 { row0: b1, row1: b0, row2: b2, row3: b3 };
    lemma_det_swap_rows_13(m1);
    additive_group_lemmas::lemma_neg_congruence(det(m1), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m1).neg(), db.neg().neg(), db);
    let m2 = Mat4x4 { row0: b1, row1: b3, row2: b2, row3: b0 };
    T::axiom_eqv_transitive(det(m2), det(m1).neg(), db);
    lemma_det_swap_rows_23(m2);
    additive_group_lemmas::lemma_neg_congruence(det(m2), db);
    let d_3a = det(Mat4x4 { row0: b1, row1: b3, row2: b0, row3: b2 });
    T::axiom_eqv_transitive(d_3a, det(m2).neg(), db.neg());

    ring_lemmas::lemma_mul_congruence_right(a3.z, d_3a, db.neg());
    ring_lemmas::lemma_mul_neg_right(a3.z, db);
    T::axiom_eqv_transitive(
        a3.z.mul(d_3a), a3.z.mul(db.neg()), a3.z.mul(db).neg());
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b3, row2: b0, row3: ab.row3 }),
        a3.z.mul(d_3a), a3.z.mul(db).neg());

    //  t0 ≡ a2.x * (-(a3.z*db)) ≡ -((a2.x*a3.z)*db)
    ring_lemmas::lemma_mul_congruence_right(a2.x,
        det(Mat4x4 { row0: b1, row1: b3, row2: b0, row3: ab.row3 }),
        a3.z.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a2.x, a3.z.mul(db));
    T::axiom_eqv_transitive(t0, a2.x.mul(a3.z.mul(db).neg()), a2.x.mul(a3.z.mul(db)).neg());
    T::axiom_mul_associative(a2.x, a3.z, db);
    T::axiom_eqv_symmetric(a2.x.mul(a3.z).mul(db), a2.x.mul(a3.z.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a2.x.mul(a3.z.mul(db)), a2.x.mul(a3.z).mul(db));
    T::axiom_eqv_transitive(t0, a2.x.mul(a3.z.mul(db)).neg(), a2.x.mul(a3.z).mul(db).neg());

    //  ---- Sub-branch 3b: det(b1,b3,b2,ABr3) → a3.x * db ----
    lemma_det_expand_fourth_row_4(b1, b3, b2,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_03(b1, b3, b2);
    lemma_det_zero_repeated_row_23(b1, b3, b2);
    lemma_det_zero_repeated_row_13(b1, b3, b2);
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b1, row1: b3, row2: b2, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b1, row1: b3, row2: b2, row3: b2 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b1, row1: b3, row2: b2, row3: b3 }));
    let (w0, w1, w2, w3) = (
        a3.x.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b2, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b2, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b2, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b2, row3: b3 })),
    );
    lemma_sum4_kill_second_third_fourth(w0, w1, w2, w3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b3, row2: b2, row3: ab.row3 }),
        w0.add(w1).add(w2).add(w3),
        a3.x.mul(det(Mat4x4 { row0: b1, row1: b3, row2: b2, row3: b0 })));

    //  det(b1,b3,b2,b0) ≡ db by double swap: swap_01 + swap_13 (already computed m2)
    let d_3b = det(Mat4x4 { row0: b1, row1: b3, row2: b2, row3: b0 });
    //  det(m2) ≡ db (already established above)
    //  d_3b = det(m2), same matrix
    //  But we need to verify: m2 = {b1,b3,b2,b0} and d_3b = det({b1,b3,b2,b0})
    //  So d_3b ≡ db

    ring_lemmas::lemma_mul_congruence_right(a3.x, d_3b, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b3, row2: b2, row3: ab.row3 }),
        a3.x.mul(d_3b), a3.x.mul(db));

    //  t2 ≡ a2.z * (a3.x * db) ≡ (a2.z*a3.x)*db
    ring_lemmas::lemma_mul_congruence_right(a2.z,
        det(Mat4x4 { row0: b1, row1: b3, row2: b2, row3: ab.row3 }),
        a3.x.mul(db));
    T::axiom_mul_associative(a2.z, a3.x, db);
    T::axiom_eqv_symmetric(a2.z.mul(a3.x).mul(db), a2.z.mul(a3.x.mul(db)));
    T::axiom_eqv_transitive(t2, a2.z.mul(a3.x.mul(db)), a2.z.mul(a3.x).mul(db));

    //  ---- Combine: t0+t2, negative first → commute then factor ----
    T::axiom_add_congruence_left(t0, a2.x.mul(a3.z).mul(db).neg(), t2);
    additive_group_lemmas::lemma_add_congruence_right(
        a2.x.mul(a3.z).mul(db).neg(), t2, a2.z.mul(a3.x).mul(db));
    T::axiom_eqv_transitive(t0.add(t2),
        a2.x.mul(a3.z).mul(db).neg().add(t2),
        a2.x.mul(a3.z).mul(db).neg().add(a2.z.mul(a3.x).mul(db)));

    let p = a2.z.mul(a3.x);
    let q = a2.x.mul(a3.z);
    T::axiom_add_commutative(q.mul(db).neg(), p.mul(db));
    T::axiom_eqv_transitive(t0.add(t2),
        q.mul(db).neg().add(p.mul(db)),
        p.mul(db).add(q.mul(db).neg()));

    T::axiom_sub_is_add_neg(p.mul(db), q.mul(db));
    T::axiom_eqv_symmetric(
        p.mul(db).sub(q.mul(db)), p.mul(db).add(q.mul(db).neg()));
    ring_lemmas::lemma_sub_mul_right(p, q, db);
    T::axiom_eqv_symmetric(p.sub(q).mul(db), p.mul(db).sub(q.mul(db)));
    T::axiom_eqv_transitive(
        p.mul(db).add(q.mul(db).neg()),
        p.mul(db).sub(q.mul(db)),
        p.sub(q).mul(db));
    T::axiom_eqv_transitive(t0.add(t2),
        p.mul(db).add(q.mul(db).neg()),
        p.sub(q).mul(db));

    //  p.sub(q) ≡ cross.z.neg() via neg_sub
    let cx = cross(drop_y(a2), drop_y(a3));
    lemma_neg_sub(q, p);
    T::axiom_eqv_symmetric(q.sub(p).neg(), p.sub(q));
    T::axiom_mul_congruence_left(p.sub(q), cx.z.neg(), db);
    T::axiom_eqv_transitive(t0.add(t2), p.sub(q).mul(db), cx.z.neg().mul(db));
    ring_lemmas::lemma_mul_neg_left(cx.z, db);
    T::axiom_eqv_transitive(t0.add(t2), cx.z.neg().mul(db), cx.z.mul(db).neg());

    //  Final chain
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: b3, row2: ab.row2, row3: ab.row3 }),
        t0.add(t2), cx.z.mul(db).neg());
}

//  ===========================================================================
//  Section 6: Col1 main
//  det(b1, ABr1, ABr2, ABr3) ≡ cofactor_vec(a1,a2,a3).y * det(b)
//  ===========================================================================

///  Column 1 of det multiplicative:
///  det(b1, ABr1, ABr2, ABr3) ≡ cofactor_vec(a1, a2, a3).y * det(b)
pub proof fn lemma_det_mul_col1<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row1, row1: mat_mul(a,b).row1,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cofactor_vec(a.row1, a.row2, a.row3).y.mul(det(b))),
{
    let a1 = a.row1;
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let ab = mat_mul(a, b);
    let db = det(b);
    let cx = cross(drop_y(a.row2), drop_y(a.row3));

    //  Expand row 1 (ABr1) → 4 terms
    lemma_det_expand_second_row_4(b1,
        a1.x, b0, a1.y, b1, a1.z, b2, a1.w, b3, ab.row2, ab.row3);

    //  Kill second (repeated rows 01: b1=b1)
    lemma_det_zero_repeated_row_01(b1, ab.row2, ab.row3);
    lemma_mul_zero_by_eqv(a1.y,
        det(Mat4x4 { row0: b1, row1: b1, row2: ab.row2, row3: ab.row3 }));

    let (e0, e1, e2, e3) = (
        a1.x.mul(det(Mat4x4 { row0: b1, row1: b0, row2: ab.row2, row3: ab.row3 })),
        a1.y.mul(det(Mat4x4 { row0: b1, row1: b1, row2: ab.row2, row3: ab.row3 })),
        a1.z.mul(det(Mat4x4 { row0: b1, row1: b2, row2: ab.row2, row3: ab.row3 })),
        a1.w.mul(det(Mat4x4 { row0: b1, row1: b3, row2: ab.row2, row3: ab.row3 })),
    );
    lemma_sum4_kill_second(e0, e1, e2, e3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        e0.add(e1).add(e2).add(e3), e0.add(e2).add(e3));

    //  Branch results
    lemma_col1_branch1(a, b);
    lemma_col1_branch2(a, b);
    lemma_col1_branch3(a, b);

    //  Each: a1.i * det(...) ≡ a1.i * (cx.j.mul(db).neg())
    //  → a1.i * (-(cx.j*db)) ≡ -(a1.i * cx.j * db) ≡ -((a1.i*cx.j)*db)
    ring_lemmas::lemma_mul_congruence_right(a1.x,
        det(Mat4x4 { row0: b1, row1: b0, row2: ab.row2, row3: ab.row3 }),
        cx.x.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a1.x, cx.x.mul(db));
    T::axiom_eqv_transitive(e0, a1.x.mul(cx.x.mul(db).neg()), a1.x.mul(cx.x.mul(db)).neg());
    T::axiom_mul_associative(a1.x, cx.x, db);
    T::axiom_eqv_symmetric(a1.x.mul(cx.x).mul(db), a1.x.mul(cx.x.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a1.x.mul(cx.x.mul(db)), a1.x.mul(cx.x).mul(db));
    T::axiom_eqv_transitive(e0, a1.x.mul(cx.x.mul(db)).neg(), a1.x.mul(cx.x).mul(db).neg());

    ring_lemmas::lemma_mul_congruence_right(a1.z,
        det(Mat4x4 { row0: b1, row1: b2, row2: ab.row2, row3: ab.row3 }),
        cx.y.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a1.z, cx.y.mul(db));
    T::axiom_eqv_transitive(e2, a1.z.mul(cx.y.mul(db).neg()), a1.z.mul(cx.y.mul(db)).neg());
    T::axiom_mul_associative(a1.z, cx.y, db);
    T::axiom_eqv_symmetric(a1.z.mul(cx.y).mul(db), a1.z.mul(cx.y.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a1.z.mul(cx.y.mul(db)), a1.z.mul(cx.y).mul(db));
    T::axiom_eqv_transitive(e2, a1.z.mul(cx.y.mul(db)).neg(), a1.z.mul(cx.y).mul(db).neg());

    ring_lemmas::lemma_mul_congruence_right(a1.w,
        det(Mat4x4 { row0: b1, row1: b3, row2: ab.row2, row3: ab.row3 }),
        cx.z.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a1.w, cx.z.mul(db));
    T::axiom_eqv_transitive(e3, a1.w.mul(cx.z.mul(db).neg()), a1.w.mul(cx.z.mul(db)).neg());
    T::axiom_mul_associative(a1.w, cx.z, db);
    T::axiom_eqv_symmetric(a1.w.mul(cx.z).mul(db), a1.w.mul(cx.z.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a1.w.mul(cx.z.mul(db)), a1.w.mul(cx.z).mul(db));
    T::axiom_eqv_transitive(e3, a1.w.mul(cx.z.mul(db)).neg(), a1.w.mul(cx.z).mul(db).neg());

    //  3-sum congruence: e0+e2+e3 ≡ -(A*db) + -(B*db) + -(C*db)
    let aa = a1.x.mul(cx.x);
    let bb = a1.z.mul(cx.y);
    let cc = a1.w.mul(cx.z);
    lemma_add_congruence_3(
        e0, aa.mul(db).neg(),
        e2, bb.mul(db).neg(),
        e3, cc.mul(db).neg());

    //  Pull negation through: -(A*db) + -(B*db) + -(C*db) ≡ -((A*db) + (B*db) + (C*db))
    //  Using neg_add twice
    additive_group_lemmas::lemma_neg_add(aa.mul(db), bb.mul(db));
    T::axiom_eqv_symmetric(
        aa.mul(db).add(bb.mul(db)).neg(),
        aa.mul(db).neg().add(bb.mul(db).neg()));
    //  -(A*db).add(-(B*db)) ≡ -((A*db)+(B*db))
    T::axiom_add_congruence_left(
        aa.mul(db).neg().add(bb.mul(db).neg()),
        aa.mul(db).add(bb.mul(db)).neg(),
        cc.mul(db).neg());
    //  -((A*db)+(B*db)).add(-(C*db)) ≡ -((A*db)+(B*db)+(C*db))
    additive_group_lemmas::lemma_neg_add(aa.mul(db).add(bb.mul(db)), cc.mul(db));
    T::axiom_eqv_symmetric(
        aa.mul(db).add(bb.mul(db)).add(cc.mul(db)).neg(),
        aa.mul(db).add(bb.mul(db)).neg().add(cc.mul(db).neg()));
    T::axiom_eqv_transitive(
        aa.mul(db).neg().add(bb.mul(db).neg()).add(cc.mul(db).neg()),
        aa.mul(db).add(bb.mul(db)).neg().add(cc.mul(db).neg()),
        aa.mul(db).add(bb.mul(db)).add(cc.mul(db)).neg());

    //  Factor inner: (A*db + B*db + C*db) ≡ (A+B+C)*db
    lemma_factor_3(aa, bb, cc, db);
    //  Negate: -((A+B+C)*db)
    additive_group_lemmas::lemma_neg_congruence(
        aa.mul(db).add(bb.mul(db)).add(cc.mul(db)),
        aa.add(bb).add(cc).mul(db));
    T::axiom_eqv_transitive(
        aa.mul(db).neg().add(bb.mul(db).neg()).add(cc.mul(db).neg()),
        aa.mul(db).add(bb.mul(db)).add(cc.mul(db)).neg(),
        aa.add(bb).add(cc).mul(db).neg());

    //  (A+B+C) = dot(drop_y(a1), cx) = triple(dy1,dy2,dy3) definitionally
    //  -((A+B+C)*db) ≡ cofactor_vec.y * db by mul_neg_left (symmetric)
    //  cofactor_vec.y = triple.neg(), so cofactor_vec.y.mul(db) ≡ triple.mul(db).neg()
    ring_lemmas::lemma_mul_neg_left(aa.add(bb).add(cc), db);
    //  triple.neg().mul(db) ≡ -(triple.mul(db)) = -(aa.add(bb).add(cc).mul(db))
    T::axiom_eqv_symmetric(
        aa.add(bb).add(cc).neg().mul(db),
        aa.add(bb).add(cc).mul(db).neg());
    T::axiom_eqv_transitive(
        aa.mul(db).neg().add(bb.mul(db).neg()).add(cc.mul(db).neg()),
        aa.add(bb).add(cc).mul(db).neg(),
        cofactor_vec(a1, a.row2, a.row3).y.mul(db));

    //  Chain: det ≡ 3-sum ≡ neg-factored ≡ cofactor_vec.y * db
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        e0.add(e2).add(e3),
        aa.mul(db).neg().add(bb.mul(db).neg()).add(cc.mul(db).neg()));
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b1, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        aa.mul(db).neg().add(bb.mul(db).neg()).add(cc.mul(db).neg()),
        cofactor_vec(a1, a.row2, a.row3).y.mul(db));
}

//  ===========================================================================
//  Section 7: Col2 branch helpers (positive sign, like col0, uses drop_z)
//  ===========================================================================

///  Branch 1 (col2): det(b2, b0, ABr2, ABr3) ≡ cross(drop_z(a2),drop_z(a3)).x * det(b)
proof fn lemma_col2_branch1<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row2, row1: b.row0,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cross(drop_z(a.row2), drop_z(a.row3)).x.mul(det(b))),
{
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let a2 = a.row2;
    let a3 = a.row3;
    let ab = mat_mul(a, b);
    let db = det(b);

    //  Expand row 2 (ABr2)
    lemma_det_expand_third_row_4(b2, b0,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    //  Kill terms 0 (row12: b0=b0), 2 (row02: b2=b2)
    lemma_det_zero_repeated_row_12(b2, b0, ab.row3);
    lemma_det_zero_repeated_row_02(b2, b0, ab.row3);
    lemma_mul_zero_by_eqv(a2.x,
        det(Mat4x4 { row0: b2, row1: b0, row2: b0, row3: ab.row3 }));
    lemma_mul_zero_by_eqv(a2.z,
        det(Mat4x4 { row0: b2, row1: b0, row2: b2, row3: ab.row3 }));

    let (t0, t1, t2, t3) = (
        a2.x.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b0, row3: ab.row3 })),
        a2.y.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b1, row3: ab.row3 })),
        a2.z.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b2, row3: ab.row3 })),
        a2.w.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b3, row3: ab.row3 })),
    );
    lemma_sum4_kill_first_third(t0, t1, t2, t3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b0, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1).add(t2).add(t3), t1.add(t3));

    //  ---- Sub-branch 1a: det(b2,b0,b1,ABr3) → a3.w * db ----
    lemma_det_expand_fourth_row_4(b2, b0, b1,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_13(b2, b0, b1);
    lemma_det_zero_repeated_row_23(b2, b0, b1);
    lemma_det_zero_repeated_row_03(b2, b0, b1);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b2, row1: b0, row2: b1, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b2, row1: b0, row2: b1, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b2, row1: b0, row2: b1, row3: b2 }));
    let (u0, u1, u2, u3) = (
        a3.x.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b1, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b1, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b1, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b1, row3: b3 })),
    );
    lemma_sum4_kill_first_second_third(u0, u1, u2, u3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b0, row2: b1, row3: ab.row3 }),
        u0.add(u1).add(u2).add(u3),
        a3.w.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b1, row3: b3 })));

    //  det(b2,b0,b1,b3) ≡ db by swap_12(b) then swap_01
    lemma_det_swap_rows_12(b);
    let m1a = Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b3 };
    lemma_det_swap_rows_01(m1a);
    additive_group_lemmas::lemma_neg_congruence(det(m1a), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m1a).neg(), db.neg().neg(), db);
    let d_1a = det(Mat4x4 { row0: b2, row1: b0, row2: b1, row3: b3 });
    T::axiom_eqv_transitive(d_1a, det(m1a).neg(), db);

    ring_lemmas::lemma_mul_congruence_right(a3.w, d_1a, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b0, row2: b1, row3: ab.row3 }),
        a3.w.mul(d_1a), a3.w.mul(db));

    //  t1 ≡ a2.y * (a3.w * db) ≡ (a2.y*a3.w)*db
    ring_lemmas::lemma_mul_congruence_right(a2.y,
        det(Mat4x4 { row0: b2, row1: b0, row2: b1, row3: ab.row3 }),
        a3.w.mul(db));
    T::axiom_mul_associative(a2.y, a3.w, db);
    T::axiom_eqv_symmetric(a2.y.mul(a3.w).mul(db), a2.y.mul(a3.w.mul(db)));
    T::axiom_eqv_transitive(t1, a2.y.mul(a3.w.mul(db)), a2.y.mul(a3.w).mul(db));

    //  ---- Sub-branch 1b: det(b2,b0,b3,ABr3) → a3.y * (-db) ----
    lemma_det_expand_fourth_row_4(b2, b0, b3,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_13(b2, b0, b3);
    lemma_det_zero_repeated_row_03(b2, b0, b3);
    lemma_det_zero_repeated_row_23(b2, b0, b3);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b2, row1: b0, row2: b3, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b2, row1: b0, row2: b3, row3: b2 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b2, row1: b0, row2: b3, row3: b3 }));
    let (v0, v1, v2, v3) = (
        a3.x.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b3, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b3, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b3, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b3, row3: b3 })),
    );
    lemma_sum4_kill_first_third_fourth(v0, v1, v2, v3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b0, row2: b3, row3: ab.row3 }),
        v0.add(v1).add(v2).add(v3),
        a3.y.mul(det(Mat4x4 { row0: b2, row1: b0, row2: b3, row3: b1 })));

    //  det(b2,b0,b3,b1) ≡ -db by swap_12(b), swap_23, swap_01
    //  m1a = {b0,b2,b1,b3} already established: det(m1a) ≡ db.neg()
    lemma_det_swap_rows_23(m1a);
    let m1b = Mat4x4 { row0: b0, row1: b2, row2: b3, row3: b1 };
    additive_group_lemmas::lemma_neg_congruence(det(m1a), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m1a).neg(), db.neg().neg(), db);
    T::axiom_eqv_transitive(det(m1b), det(m1a).neg(), db);
    lemma_det_swap_rows_01(m1b);
    additive_group_lemmas::lemma_neg_congruence(det(m1b), db);
    let d_1b = det(Mat4x4 { row0: b2, row1: b0, row2: b3, row3: b1 });
    T::axiom_eqv_transitive(d_1b, det(m1b).neg(), db.neg());

    ring_lemmas::lemma_mul_congruence_right(a3.y, d_1b, db.neg());
    ring_lemmas::lemma_mul_neg_right(a3.y, db);
    T::axiom_eqv_transitive(
        a3.y.mul(d_1b), a3.y.mul(db.neg()), a3.y.mul(db).neg());
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b0, row2: b3, row3: ab.row3 }),
        a3.y.mul(d_1b), a3.y.mul(db).neg());

    //  t3 ≡ a2.w * (-(a3.y*db)) ≡ -((a2.w*a3.y)*db)
    ring_lemmas::lemma_mul_congruence_right(a2.w,
        det(Mat4x4 { row0: b2, row1: b0, row2: b3, row3: ab.row3 }),
        a3.y.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a2.w, a3.y.mul(db));
    T::axiom_eqv_transitive(t3, a2.w.mul(a3.y.mul(db).neg()), a2.w.mul(a3.y.mul(db)).neg());
    T::axiom_mul_associative(a2.w, a3.y, db);
    T::axiom_eqv_symmetric(a2.w.mul(a3.y).mul(db), a2.w.mul(a3.y.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a2.w.mul(a3.y.mul(db)), a2.w.mul(a3.y).mul(db));
    T::axiom_eqv_transitive(t3, a2.w.mul(a3.y.mul(db)).neg(), a2.w.mul(a3.y).mul(db).neg());

    //  Combine: t1+t3, positive first, no commute needed
    T::axiom_add_congruence_left(t1, a2.y.mul(a3.w).mul(db), t3);
    additive_group_lemmas::lemma_add_congruence_right(
        a2.y.mul(a3.w).mul(db), t3, a2.w.mul(a3.y).mul(db).neg());
    T::axiom_eqv_transitive(t1.add(t3),
        a2.y.mul(a3.w).mul(db).add(t3),
        a2.y.mul(a3.w).mul(db).add(a2.w.mul(a3.y).mul(db).neg()));

    let p = a2.y.mul(a3.w);
    let q = a2.w.mul(a3.y);
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
        cross(drop_z(a2), drop_z(a3)).x.mul(db));

    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b0, row2: ab.row2, row3: ab.row3 }),
        t1.add(t3),
        cross(drop_z(a2), drop_z(a3)).x.mul(db));
}

///  Branch 2 (col2): det(b2, b1, ABr2, ABr3) ≡ cross(drop_z(a2),drop_z(a3)).y * det(b)
proof fn lemma_col2_branch2<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row2, row1: b.row1,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cross(drop_z(a.row2), drop_z(a.row3)).y.mul(det(b))),
{
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let a2 = a.row2;
    let a3 = a.row3;
    let ab = mat_mul(a, b);
    let db = det(b);

    lemma_det_expand_third_row_4(b2, b1,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    //  Kill terms 1 (row12: b1=b1), 2 (row02: b2=b2)
    lemma_det_zero_repeated_row_12(b2, b1, ab.row3);
    lemma_det_zero_repeated_row_02(b2, b1, ab.row3);
    lemma_mul_zero_by_eqv(a2.y,
        det(Mat4x4 { row0: b2, row1: b1, row2: b1, row3: ab.row3 }));
    lemma_mul_zero_by_eqv(a2.z,
        det(Mat4x4 { row0: b2, row1: b1, row2: b2, row3: ab.row3 }));

    let (t0, t1, t2, t3) = (
        a2.x.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: ab.row3 })),
        a2.y.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b1, row3: ab.row3 })),
        a2.z.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b2, row3: ab.row3 })),
        a2.w.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b3, row3: ab.row3 })),
    );
    lemma_sum4_kill_second_third(t0, t1, t2, t3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b1, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1).add(t2).add(t3), t0.add(t3));

    //  ---- Sub-branch 2a: det(b2,b1,b0,ABr3) → a3.w * (-db) ----
    lemma_det_expand_fourth_row_4(b2, b1, b0,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_23(b2, b1, b0);
    lemma_det_zero_repeated_row_13(b2, b1, b0);
    lemma_det_zero_repeated_row_03(b2, b1, b0);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: b2 }));
    let (u0, u1, u2, u3) = (
        a3.x.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: b3 })),
    );
    lemma_sum4_kill_first_second_third(u0, u1, u2, u3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: ab.row3 }),
        u0.add(u1).add(u2).add(u3),
        a3.w.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: b3 })));

    //  det(b2,b1,b0,b3) ≡ -db by swap_02(b)
    lemma_det_swap_rows_02(b);
    ring_lemmas::lemma_mul_congruence_right(a3.w,
        det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: b3 }), db.neg());
    ring_lemmas::lemma_mul_neg_right(a3.w, db);
    T::axiom_eqv_transitive(
        a3.w.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: b3 })),
        a3.w.mul(db.neg()), a3.w.mul(db).neg());
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: ab.row3 }),
        a3.w.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: b3 })),
        a3.w.mul(db).neg());

    //  t0 ≡ a2.x * (-(a3.w*db)) ≡ -((a2.x*a3.w)*db)
    ring_lemmas::lemma_mul_congruence_right(a2.x,
        det(Mat4x4 { row0: b2, row1: b1, row2: b0, row3: ab.row3 }),
        a3.w.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a2.x, a3.w.mul(db));
    T::axiom_eqv_transitive(t0, a2.x.mul(a3.w.mul(db).neg()), a2.x.mul(a3.w.mul(db)).neg());
    T::axiom_mul_associative(a2.x, a3.w, db);
    T::axiom_eqv_symmetric(a2.x.mul(a3.w).mul(db), a2.x.mul(a3.w.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a2.x.mul(a3.w.mul(db)), a2.x.mul(a3.w).mul(db));
    T::axiom_eqv_transitive(t0, a2.x.mul(a3.w.mul(db)).neg(), a2.x.mul(a3.w).mul(db).neg());

    //  ---- Sub-branch 2b: det(b2,b1,b3,ABr3) → a3.x * db ----
    lemma_det_expand_fourth_row_4(b2, b1, b3,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_13(b2, b1, b3);
    lemma_det_zero_repeated_row_03(b2, b1, b3);
    lemma_det_zero_repeated_row_23(b2, b1, b3);
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b2, row1: b1, row2: b3, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b2, row1: b1, row2: b3, row3: b2 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b2, row1: b1, row2: b3, row3: b3 }));
    let (w0, w1, w2, w3) = (
        a3.x.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b3, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b3, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b3, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b3, row3: b3 })),
    );
    lemma_sum4_kill_second_third_fourth(w0, w1, w2, w3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b1, row2: b3, row3: ab.row3 }),
        w0.add(w1).add(w2).add(w3),
        a3.x.mul(det(Mat4x4 { row0: b2, row1: b1, row2: b3, row3: b0 })));

    //  det(b2,b1,b3,b0) ≡ db by swap_23(b) then swap_03
    lemma_det_swap_rows_23(b);
    let m2b = Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 };
    lemma_det_swap_rows_03(m2b);
    additive_group_lemmas::lemma_neg_congruence(det(m2b), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m2b).neg(), db.neg().neg(), db);
    let d_2b = det(Mat4x4 { row0: b2, row1: b1, row2: b3, row3: b0 });
    T::axiom_eqv_transitive(d_2b, det(m2b).neg(), db);

    ring_lemmas::lemma_mul_congruence_right(a3.x, d_2b, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b1, row2: b3, row3: ab.row3 }),
        a3.x.mul(d_2b), a3.x.mul(db));

    //  t3 ≡ a2.w * (a3.x * db) ≡ (a2.w*a3.x)*db
    ring_lemmas::lemma_mul_congruence_right(a2.w,
        det(Mat4x4 { row0: b2, row1: b1, row2: b3, row3: ab.row3 }),
        a3.x.mul(db));
    T::axiom_mul_associative(a2.w, a3.x, db);
    T::axiom_eqv_symmetric(a2.w.mul(a3.x).mul(db), a2.w.mul(a3.x.mul(db)));
    T::axiom_eqv_transitive(t3, a2.w.mul(a3.x.mul(db)), a2.w.mul(a3.x).mul(db));

    //  Combine: t0+t3, negative first → commute
    T::axiom_add_congruence_left(t0, a2.x.mul(a3.w).mul(db).neg(), t3);
    additive_group_lemmas::lemma_add_congruence_right(
        a2.x.mul(a3.w).mul(db).neg(), t3, a2.w.mul(a3.x).mul(db));
    T::axiom_eqv_transitive(t0.add(t3),
        a2.x.mul(a3.w).mul(db).neg().add(t3),
        a2.x.mul(a3.w).mul(db).neg().add(a2.w.mul(a3.x).mul(db)));

    let p = a2.w.mul(a3.x);
    let q = a2.x.mul(a3.w);
    T::axiom_add_commutative(q.mul(db).neg(), p.mul(db));
    T::axiom_eqv_transitive(t0.add(t3),
        q.mul(db).neg().add(p.mul(db)),
        p.mul(db).add(q.mul(db).neg()));

    T::axiom_sub_is_add_neg(p.mul(db), q.mul(db));
    T::axiom_eqv_symmetric(
        p.mul(db).sub(q.mul(db)), p.mul(db).add(q.mul(db).neg()));
    ring_lemmas::lemma_sub_mul_right(p, q, db);
    T::axiom_eqv_symmetric(p.sub(q).mul(db), p.mul(db).sub(q.mul(db)));
    T::axiom_eqv_transitive(
        p.mul(db).add(q.mul(db).neg()),
        p.mul(db).sub(q.mul(db)),
        p.sub(q).mul(db));
    T::axiom_eqv_transitive(t0.add(t3),
        p.mul(db).add(q.mul(db).neg()),
        cross(drop_z(a2), drop_z(a3)).y.mul(db));

    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b1, row2: ab.row2, row3: ab.row3 }),
        t0.add(t3),
        cross(drop_z(a2), drop_z(a3)).y.mul(db));
}

///  Branch 3 (col2): det(b2, b3, ABr2, ABr3) ≡ cross(drop_z(a2),drop_z(a3)).z * det(b)
proof fn lemma_col2_branch3<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row2, row1: b.row3,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cross(drop_z(a.row2), drop_z(a.row3)).z.mul(det(b))),
{
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let a2 = a.row2;
    let a3 = a.row3;
    let ab = mat_mul(a, b);
    let db = det(b);

    lemma_det_expand_third_row_4(b2, b3,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    //  Kill terms 2 (row02: b2=b2), 3 (row12: b3=b3)
    lemma_det_zero_repeated_row_02(b2, b3, ab.row3);
    lemma_det_zero_repeated_row_12(b2, b3, ab.row3);
    lemma_mul_zero_by_eqv(a2.z,
        det(Mat4x4 { row0: b2, row1: b3, row2: b2, row3: ab.row3 }));
    lemma_mul_zero_by_eqv(a2.w,
        det(Mat4x4 { row0: b2, row1: b3, row2: b3, row3: ab.row3 }));

    let (t0, t1, t2, t3) = (
        a2.x.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b0, row3: ab.row3 })),
        a2.y.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b1, row3: ab.row3 })),
        a2.z.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b2, row3: ab.row3 })),
        a2.w.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b3, row3: ab.row3 })),
    );
    lemma_sum4_kill_third_fourth(t0, t1, t2, t3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b3, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1).add(t2).add(t3), t0.add(t1));

    //  ---- Sub-branch 3a: det(b2,b3,b0,ABr3) → a3.y * db ----
    lemma_det_expand_fourth_row_4(b2, b3, b0,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_23(b2, b3, b0);
    lemma_det_zero_repeated_row_03(b2, b3, b0);
    lemma_det_zero_repeated_row_13(b2, b3, b0);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b2, row1: b3, row2: b0, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b2, row1: b3, row2: b0, row3: b2 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b2, row1: b3, row2: b0, row3: b3 }));
    let (u0, u1, u2, u3) = (
        a3.x.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b0, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b0, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b0, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b0, row3: b3 })),
    );
    lemma_sum4_kill_first_third_fourth(u0, u1, u2, u3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b3, row2: b0, row3: ab.row3 }),
        u0.add(u1).add(u2).add(u3),
        a3.y.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b0, row3: b1 })));

    //  det(b2,b3,b0,b1) ≡ db by swap_13(b) then swap_02
    lemma_det_swap_rows_13(b);
    let m3a = Mat4x4 { row0: b0, row1: b3, row2: b2, row3: b1 };
    lemma_det_swap_rows_02(m3a);
    additive_group_lemmas::lemma_neg_congruence(det(m3a), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m3a).neg(), db.neg().neg(), db);
    let d_3a = det(Mat4x4 { row0: b2, row1: b3, row2: b0, row3: b1 });
    T::axiom_eqv_transitive(d_3a, det(m3a).neg(), db);

    ring_lemmas::lemma_mul_congruence_right(a3.y, d_3a, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b3, row2: b0, row3: ab.row3 }),
        a3.y.mul(d_3a), a3.y.mul(db));

    //  t0 ≡ a2.x * (a3.y * db) ≡ (a2.x*a3.y)*db
    ring_lemmas::lemma_mul_congruence_right(a2.x,
        det(Mat4x4 { row0: b2, row1: b3, row2: b0, row3: ab.row3 }),
        a3.y.mul(db));
    T::axiom_mul_associative(a2.x, a3.y, db);
    T::axiom_eqv_symmetric(a2.x.mul(a3.y).mul(db), a2.x.mul(a3.y.mul(db)));
    T::axiom_eqv_transitive(t0, a2.x.mul(a3.y.mul(db)), a2.x.mul(a3.y).mul(db));

    //  ---- Sub-branch 3b: det(b2,b3,b1,ABr3) → a3.x * (-db) ----
    lemma_det_expand_fourth_row_4(b2, b3, b1,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_23(b2, b3, b1);
    lemma_det_zero_repeated_row_03(b2, b3, b1);
    lemma_det_zero_repeated_row_13(b2, b3, b1);
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b2, row1: b3, row2: b1, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b2, row1: b3, row2: b1, row3: b2 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b2, row1: b3, row2: b1, row3: b3 }));
    let (w0, w1, w2, w3) = (
        a3.x.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b1, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b1, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b1, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b1, row3: b3 })),
    );
    lemma_sum4_kill_second_third_fourth(w0, w1, w2, w3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b3, row2: b1, row3: ab.row3 }),
        w0.add(w1).add(w2).add(w3),
        a3.x.mul(det(Mat4x4 { row0: b2, row1: b3, row2: b1, row3: b0 })));

    //  det(b2,b3,b1,b0) ≡ -db by swap_23(b), swap_12, swap_03
    lemma_det_swap_rows_23(b);
    let n1 = Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 };
    lemma_det_swap_rows_12(n1);
    additive_group_lemmas::lemma_neg_congruence(det(n1), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(n1).neg(), db.neg().neg(), db);
    let n2 = Mat4x4 { row0: b0, row1: b3, row2: b1, row3: b2 };
    T::axiom_eqv_transitive(det(n2), det(n1).neg(), db);
    lemma_det_swap_rows_03(n2);
    additive_group_lemmas::lemma_neg_congruence(det(n2), db);
    let d_3b = det(Mat4x4 { row0: b2, row1: b3, row2: b1, row3: b0 });
    T::axiom_eqv_transitive(d_3b, det(n2).neg(), db.neg());

    ring_lemmas::lemma_mul_congruence_right(a3.x, d_3b, db.neg());
    ring_lemmas::lemma_mul_neg_right(a3.x, db);
    T::axiom_eqv_transitive(
        a3.x.mul(d_3b), a3.x.mul(db.neg()), a3.x.mul(db).neg());
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b3, row2: b1, row3: ab.row3 }),
        a3.x.mul(d_3b), a3.x.mul(db).neg());

    //  t1 ≡ a2.y * (-(a3.x*db)) ≡ -((a2.y*a3.x)*db)
    ring_lemmas::lemma_mul_congruence_right(a2.y,
        det(Mat4x4 { row0: b2, row1: b3, row2: b1, row3: ab.row3 }),
        a3.x.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a2.y, a3.x.mul(db));
    T::axiom_eqv_transitive(t1, a2.y.mul(a3.x.mul(db).neg()), a2.y.mul(a3.x.mul(db)).neg());
    T::axiom_mul_associative(a2.y, a3.x, db);
    T::axiom_eqv_symmetric(a2.y.mul(a3.x).mul(db), a2.y.mul(a3.x.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a2.y.mul(a3.x.mul(db)), a2.y.mul(a3.x).mul(db));
    T::axiom_eqv_transitive(t1, a2.y.mul(a3.x.mul(db)).neg(), a2.y.mul(a3.x).mul(db).neg());

    //  Combine: t0+t1, positive first, no commute
    T::axiom_add_congruence_left(t0, a2.x.mul(a3.y).mul(db), t1);
    additive_group_lemmas::lemma_add_congruence_right(
        a2.x.mul(a3.y).mul(db), t1, a2.y.mul(a3.x).mul(db).neg());
    T::axiom_eqv_transitive(t0.add(t1),
        a2.x.mul(a3.y).mul(db).add(t1),
        a2.x.mul(a3.y).mul(db).add(a2.y.mul(a3.x).mul(db).neg()));

    let p = a2.x.mul(a3.y);
    let q = a2.y.mul(a3.x);
    T::axiom_sub_is_add_neg(p.mul(db), q.mul(db));
    T::axiom_eqv_symmetric(
        p.mul(db).sub(q.mul(db)), p.mul(db).add(q.mul(db).neg()));
    ring_lemmas::lemma_sub_mul_right(p, q, db);
    T::axiom_eqv_symmetric(p.sub(q).mul(db), p.mul(db).sub(q.mul(db)));
    T::axiom_eqv_transitive(
        p.mul(db).add(q.mul(db).neg()),
        p.mul(db).sub(q.mul(db)),
        p.sub(q).mul(db));
    T::axiom_eqv_transitive(t0.add(t1),
        p.mul(db).add(q.mul(db).neg()),
        cross(drop_z(a2), drop_z(a3)).z.mul(db));

    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: b3, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1),
        cross(drop_z(a2), drop_z(a3)).z.mul(db));
}

//  ===========================================================================
//  Section 8: Col2 main
//  ===========================================================================

///  Column 2 of det multiplicative:
///  det(b2, ABr1, ABr2, ABr3) ≡ cofactor_vec(a1, a2, a3).z * det(b)
pub proof fn lemma_det_mul_col2<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row2, row1: mat_mul(a,b).row1,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cofactor_vec(a.row1, a.row2, a.row3).z.mul(det(b))),
{
    let a1 = a.row1;
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let ab = mat_mul(a, b);
    let db = det(b);
    let cx = cross(drop_z(a.row2), drop_z(a.row3));

    //  Expand row 1 (ABr1) → 4 terms
    lemma_det_expand_second_row_4(b2,
        a1.x, b0, a1.y, b1, a1.z, b2, a1.w, b3, ab.row2, ab.row3);

    //  Kill third (repeated rows 01: b2=b2)
    lemma_det_zero_repeated_row_01(b2, ab.row2, ab.row3);
    lemma_mul_zero_by_eqv(a1.z,
        det(Mat4x4 { row0: b2, row1: b2, row2: ab.row2, row3: ab.row3 }));

    let (e0, e1, e2, e3) = (
        a1.x.mul(det(Mat4x4 { row0: b2, row1: b0, row2: ab.row2, row3: ab.row3 })),
        a1.y.mul(det(Mat4x4 { row0: b2, row1: b1, row2: ab.row2, row3: ab.row3 })),
        a1.z.mul(det(Mat4x4 { row0: b2, row1: b2, row2: ab.row2, row3: ab.row3 })),
        a1.w.mul(det(Mat4x4 { row0: b2, row1: b3, row2: ab.row2, row3: ab.row3 })),
    );
    lemma_sum4_kill_third(e0, e1, e2, e3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        e0.add(e1).add(e2).add(e3), e0.add(e1).add(e3));

    //  Branch results (positive)
    lemma_col2_branch1(a, b);
    lemma_col2_branch2(a, b);
    lemma_col2_branch3(a, b);

    //  Scale each: a1.i * (cx.j * db) ≡ (a1.i * cx.j) * db
    ring_lemmas::lemma_mul_congruence_right(a1.x,
        det(Mat4x4 { row0: b2, row1: b0, row2: ab.row2, row3: ab.row3 }),
        cx.x.mul(db));
    T::axiom_mul_associative(a1.x, cx.x, db);
    T::axiom_eqv_symmetric(a1.x.mul(cx.x).mul(db), a1.x.mul(cx.x.mul(db)));
    T::axiom_eqv_transitive(e0, a1.x.mul(cx.x.mul(db)), a1.x.mul(cx.x).mul(db));

    ring_lemmas::lemma_mul_congruence_right(a1.y,
        det(Mat4x4 { row0: b2, row1: b1, row2: ab.row2, row3: ab.row3 }),
        cx.y.mul(db));
    T::axiom_mul_associative(a1.y, cx.y, db);
    T::axiom_eqv_symmetric(a1.y.mul(cx.y).mul(db), a1.y.mul(cx.y.mul(db)));
    T::axiom_eqv_transitive(e1, a1.y.mul(cx.y.mul(db)), a1.y.mul(cx.y).mul(db));

    ring_lemmas::lemma_mul_congruence_right(a1.w,
        det(Mat4x4 { row0: b2, row1: b3, row2: ab.row2, row3: ab.row3 }),
        cx.z.mul(db));
    T::axiom_mul_associative(a1.w, cx.z, db);
    T::axiom_eqv_symmetric(a1.w.mul(cx.z).mul(db), a1.w.mul(cx.z.mul(db)));
    T::axiom_eqv_transitive(e3, a1.w.mul(cx.z.mul(db)), a1.w.mul(cx.z).mul(db));

    //  3-sum congruence
    lemma_add_congruence_3(
        e0, a1.x.mul(cx.x).mul(db),
        e1, a1.y.mul(cx.y).mul(db),
        e3, a1.w.mul(cx.z).mul(db));

    //  Factor out db
    lemma_factor_3(a1.x.mul(cx.x), a1.y.mul(cx.y), a1.w.mul(cx.z), db);

    //  Chain
    let sum_factored = a1.x.mul(cx.x).mul(db)
        .add(a1.y.mul(cx.y).mul(db))
        .add(a1.w.mul(cx.z).mul(db));

    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        e0.add(e1).add(e3), sum_factored);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b2, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        sum_factored, cofactor_vec(a1, a.row2, a.row3).z.mul(db));
}

//  ===========================================================================
//  Section 9: Col3 branch helpers (negative sign, like col1, uses drop_w)
//  Each proves det(b3, b_j, ABr2, ABr3) ≡ -cross(drop_w(a2),drop_w(a3)).component * db
//  ===========================================================================

///  Branch 1 (col3): det(b3, b0, ABr2, ABr3) ≡ cross(drop_w(a2),drop_w(a3)).x.mul(db).neg()
proof fn lemma_col3_branch1<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row3, row1: b.row0,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cross(drop_w(a.row2), drop_w(a.row3)).x.mul(det(b)).neg()),
{
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let a2 = a.row2;
    let a3 = a.row3;
    let ab = mat_mul(a, b);
    let db = det(b);

    //  ---- Expand row 2 (ABr2) ----
    lemma_det_expand_third_row_4(b3, b0,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    //  Kill terms 0 (row12: b0=b0), 3 (row02: b3=b3)
    lemma_det_zero_repeated_row_12(b3, b0, ab.row3);
    lemma_det_zero_repeated_row_02(b3, b0, ab.row3);
    lemma_mul_zero_by_eqv(a2.x,
        det(Mat4x4 { row0: b3, row1: b0, row2: b0, row3: ab.row3 }));
    lemma_mul_zero_by_eqv(a2.w,
        det(Mat4x4 { row0: b3, row1: b0, row2: b3, row3: ab.row3 }));

    let (t0, t1, t2, t3) = (
        a2.x.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b0, row3: ab.row3 })),
        a2.y.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: ab.row3 })),
        a2.z.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b2, row3: ab.row3 })),
        a2.w.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b3, row3: ab.row3 })),
    );
    lemma_sum4_kill_first_fourth(t0, t1, t2, t3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b0, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1).add(t2).add(t3), t1.add(t2));

    //  ---- Sub-branch 1a: det(b3,b0,b1,ABr3) → a3.z * (-db) ----
    lemma_det_expand_fourth_row_4(b3, b0, b1,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_13(b3, b0, b1);
    lemma_det_zero_repeated_row_23(b3, b0, b1);
    lemma_det_zero_repeated_row_03(b3, b0, b1);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: b3 }));
    let (u0, u1, u2, u3) = (
        a3.x.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: b3 })),
    );
    lemma_sum4_kill_first_second_fourth(u0, u1, u2, u3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: ab.row3 }),
        u0.add(u1).add(u2).add(u3),
        a3.z.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: b2 })));

    //  det(b3,b0,b1,b2) ≡ -db by 3 swaps
    //  swap_23(b): det(b0,b1,b3,b2) ≡ -db
    lemma_det_swap_rows_23(b);
    let m3 = Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 };
    //  swap_12(m3): det(b0,b3,b1,b2) ≡ det(m3).neg()
    lemma_det_swap_rows_12(m3);
    additive_group_lemmas::lemma_neg_congruence(det(m3), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m3).neg(), db.neg().neg(), db);
    let d_mid = det(Mat4x4 { row0: b0, row1: b3, row2: b1, row3: b2 });
    T::axiom_eqv_transitive(d_mid, det(m3).neg(), db);
    //  swap_01(m_mid): det(b3,b0,b1,b2) ≡ det(m_mid).neg() ≡ -db
    let m_mid = Mat4x4 { row0: b0, row1: b3, row2: b1, row3: b2 };
    lemma_det_swap_rows_01(m_mid);
    additive_group_lemmas::lemma_neg_congruence(d_mid, db);
    let d_1a = det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: b2 });
    T::axiom_eqv_transitive(d_1a, d_mid.neg(), db.neg());

    ring_lemmas::lemma_mul_congruence_right(a3.z, d_1a, db.neg());
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: ab.row3 }),
        a3.z.mul(d_1a), a3.z.mul(db.neg()));
    ring_lemmas::lemma_mul_neg_right(a3.z, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: ab.row3 }),
        a3.z.mul(db.neg()), a3.z.mul(db).neg());

    //  t1 ≡ a2.y * (-(a3.z*db)) ≡ -((a2.y*a3.z)*db)
    ring_lemmas::lemma_mul_congruence_right(a2.y,
        det(Mat4x4 { row0: b3, row1: b0, row2: b1, row3: ab.row3 }),
        a3.z.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a2.y, a3.z.mul(db));
    T::axiom_eqv_transitive(t1, a2.y.mul(a3.z.mul(db).neg()), a2.y.mul(a3.z.mul(db)).neg());
    T::axiom_mul_associative(a2.y, a3.z, db);
    T::axiom_eqv_symmetric(a2.y.mul(a3.z).mul(db), a2.y.mul(a3.z.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a2.y.mul(a3.z.mul(db)), a2.y.mul(a3.z).mul(db));
    T::axiom_eqv_transitive(t1, a2.y.mul(a3.z.mul(db)).neg(), a2.y.mul(a3.z).mul(db).neg());

    //  ---- Sub-branch 1b: det(b3,b0,b2,ABr3) → a3.y * db ----
    lemma_det_expand_fourth_row_4(b3, b0, b2,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_13(b3, b0, b2);
    lemma_det_zero_repeated_row_23(b3, b0, b2);
    lemma_det_zero_repeated_row_03(b3, b0, b2);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b3, row1: b0, row2: b2, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b3, row1: b0, row2: b2, row3: b2 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b3, row1: b0, row2: b2, row3: b3 }));
    let (v0, v1, v2, v3) = (
        a3.x.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b2, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b2, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b2, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b2, row3: b3 })),
    );
    lemma_sum4_kill_first_third_fourth(v0, v1, v2, v3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b0, row2: b2, row3: ab.row3 }),
        v0.add(v1).add(v2).add(v3),
        a3.y.mul(det(Mat4x4 { row0: b3, row1: b0, row2: b2, row3: b1 })));

    //  det(b3,b0,b2,b1) ≡ db by 2 swaps: swap_13(b) then swap_01
    lemma_det_swap_rows_13(b);
    let m_1b = Mat4x4 { row0: b0, row1: b3, row2: b2, row3: b1 };
    lemma_det_swap_rows_01(m_1b);
    additive_group_lemmas::lemma_neg_congruence(det(m_1b), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m_1b).neg(), db.neg().neg(), db);
    let d_1b = det(Mat4x4 { row0: b3, row1: b0, row2: b2, row3: b1 });
    T::axiom_eqv_transitive(d_1b, det(m_1b).neg(), db);

    ring_lemmas::lemma_mul_congruence_right(a3.y, d_1b, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b0, row2: b2, row3: ab.row3 }),
        a3.y.mul(d_1b), a3.y.mul(db));

    //  t2 ≡ a2.z * (a3.y * db) ≡ (a2.z*a3.y)*db
    ring_lemmas::lemma_mul_congruence_right(a2.z,
        det(Mat4x4 { row0: b3, row1: b0, row2: b2, row3: ab.row3 }),
        a3.y.mul(db));
    T::axiom_mul_associative(a2.z, a3.y, db);
    T::axiom_eqv_symmetric(a2.z.mul(a3.y).mul(db), a2.z.mul(a3.y.mul(db)));
    T::axiom_eqv_transitive(t2, a2.z.mul(a3.y.mul(db)), a2.z.mul(a3.y).mul(db));

    //  ---- Combine: t1+t2, negative first → commute then factor ----
    T::axiom_add_congruence_left(t1, a2.y.mul(a3.z).mul(db).neg(), t2);
    additive_group_lemmas::lemma_add_congruence_right(
        a2.y.mul(a3.z).mul(db).neg(), t2, a2.z.mul(a3.y).mul(db));
    T::axiom_eqv_transitive(t1.add(t2),
        a2.y.mul(a3.z).mul(db).neg().add(t2),
        a2.y.mul(a3.z).mul(db).neg().add(a2.z.mul(a3.y).mul(db)));

    let p = a2.z.mul(a3.y);
    let q = a2.y.mul(a3.z);
    T::axiom_add_commutative(q.mul(db).neg(), p.mul(db));
    T::axiom_eqv_transitive(t1.add(t2),
        q.mul(db).neg().add(p.mul(db)),
        p.mul(db).add(q.mul(db).neg()));

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
        p.sub(q).mul(db));

    //  p.sub(q) ≡ cross.x.neg() via neg_sub
    let cx = cross(drop_w(a2), drop_w(a3));
    lemma_neg_sub(q, p);
    T::axiom_eqv_symmetric(q.sub(p).neg(), p.sub(q));
    T::axiom_mul_congruence_left(p.sub(q), cx.x.neg(), db);
    T::axiom_eqv_transitive(t1.add(t2), p.sub(q).mul(db), cx.x.neg().mul(db));
    ring_lemmas::lemma_mul_neg_left(cx.x, db);
    T::axiom_eqv_transitive(t1.add(t2), cx.x.neg().mul(db), cx.x.mul(db).neg());

    //  Final chain
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b0, row2: ab.row2, row3: ab.row3 }),
        t1.add(t2), cx.x.mul(db).neg());
}

///  Branch 2 (col3): det(b3, b1, ABr2, ABr3) ≡ cross(drop_w(a2),drop_w(a3)).y.mul(db).neg()
proof fn lemma_col3_branch2<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row3, row1: b.row1,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cross(drop_w(a.row2), drop_w(a.row3)).y.mul(det(b)).neg()),
{
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let a2 = a.row2;
    let a3 = a.row3;
    let ab = mat_mul(a, b);
    let db = det(b);

    //  ---- Expand row 2 (ABr2) ----
    lemma_det_expand_third_row_4(b3, b1,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    //  Kill terms 1 (row12: b1=b1), 3 (row02: b3=b3)
    lemma_det_zero_repeated_row_12(b3, b1, ab.row3);
    lemma_det_zero_repeated_row_02(b3, b1, ab.row3);
    lemma_mul_zero_by_eqv(a2.y,
        det(Mat4x4 { row0: b3, row1: b1, row2: b1, row3: ab.row3 }));
    lemma_mul_zero_by_eqv(a2.w,
        det(Mat4x4 { row0: b3, row1: b1, row2: b3, row3: ab.row3 }));

    let (t0, t1, t2, t3) = (
        a2.x.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b0, row3: ab.row3 })),
        a2.y.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b1, row3: ab.row3 })),
        a2.z.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: ab.row3 })),
        a2.w.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b3, row3: ab.row3 })),
    );
    lemma_sum4_kill_second_fourth(t0, t1, t2, t3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b1, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1).add(t2).add(t3), t0.add(t2));

    //  ---- Sub-branch 2a: det(b3,b1,b0,ABr3) → a3.z * db ----
    lemma_det_expand_fourth_row_4(b3, b1, b0,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_23(b3, b1, b0);
    lemma_det_zero_repeated_row_13(b3, b1, b0);
    lemma_det_zero_repeated_row_03(b3, b1, b0);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b3, row1: b1, row2: b0, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b3, row1: b1, row2: b0, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b3, row1: b1, row2: b0, row3: b3 }));
    let (u0, u1, u2, u3) = (
        a3.x.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b0, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b0, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b0, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b0, row3: b3 })),
    );
    lemma_sum4_kill_first_second_fourth(u0, u1, u2, u3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b1, row2: b0, row3: ab.row3 }),
        u0.add(u1).add(u2).add(u3),
        a3.z.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b0, row3: b2 })));

    //  det(b3,b1,b0,b2) ≡ db by 2 swaps: swap_23(b) then swap_02
    lemma_det_swap_rows_23(b);
    let m_2a = Mat4x4 { row0: b0, row1: b1, row2: b3, row3: b2 };
    lemma_det_swap_rows_02(m_2a);
    additive_group_lemmas::lemma_neg_congruence(det(m_2a), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m_2a).neg(), db.neg().neg(), db);
    let d_2a = det(Mat4x4 { row0: b3, row1: b1, row2: b0, row3: b2 });
    T::axiom_eqv_transitive(d_2a, det(m_2a).neg(), db);

    ring_lemmas::lemma_mul_congruence_right(a3.z, d_2a, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b1, row2: b0, row3: ab.row3 }),
        a3.z.mul(d_2a), a3.z.mul(db));

    //  t0 ≡ a2.x * (a3.z * db) ≡ (a2.x*a3.z)*db
    ring_lemmas::lemma_mul_congruence_right(a2.x,
        det(Mat4x4 { row0: b3, row1: b1, row2: b0, row3: ab.row3 }),
        a3.z.mul(db));
    T::axiom_mul_associative(a2.x, a3.z, db);
    T::axiom_eqv_symmetric(a2.x.mul(a3.z).mul(db), a2.x.mul(a3.z.mul(db)));
    T::axiom_eqv_transitive(t0, a2.x.mul(a3.z.mul(db)), a2.x.mul(a3.z).mul(db));

    //  ---- Sub-branch 2b: det(b3,b1,b2,ABr3) → a3.x * (-db) ----
    lemma_det_expand_fourth_row_4(b3, b1, b2,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_13(b3, b1, b2);
    lemma_det_zero_repeated_row_23(b3, b1, b2);
    lemma_det_zero_repeated_row_03(b3, b1, b2);
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: b2 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: b3 }));
    let (v0, v1, v2, v3) = (
        a3.x.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: b3 })),
    );
    lemma_sum4_kill_second_third_fourth(v0, v1, v2, v3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: ab.row3 }),
        v0.add(v1).add(v2).add(v3),
        a3.x.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: b0 })));

    //  det(b3,b1,b2,b0) ≡ -db by swap_03
    lemma_det_swap_rows_03(b);
    ring_lemmas::lemma_mul_congruence_right(a3.x,
        det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: b0 }), db.neg());
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: ab.row3 }),
        a3.x.mul(det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: b0 })),
        a3.x.mul(db.neg()));
    ring_lemmas::lemma_mul_neg_right(a3.x, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: ab.row3 }),
        a3.x.mul(db.neg()), a3.x.mul(db).neg());

    //  t2 ≡ a2.z * (-(a3.x*db)) ≡ -((a2.z*a3.x)*db)
    ring_lemmas::lemma_mul_congruence_right(a2.z,
        det(Mat4x4 { row0: b3, row1: b1, row2: b2, row3: ab.row3 }),
        a3.x.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a2.z, a3.x.mul(db));
    T::axiom_eqv_transitive(t2, a2.z.mul(a3.x.mul(db).neg()), a2.z.mul(a3.x.mul(db)).neg());
    T::axiom_mul_associative(a2.z, a3.x, db);
    T::axiom_eqv_symmetric(a2.z.mul(a3.x).mul(db), a2.z.mul(a3.x.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a2.z.mul(a3.x.mul(db)), a2.z.mul(a3.x).mul(db));
    T::axiom_eqv_transitive(t2, a2.z.mul(a3.x.mul(db)).neg(), a2.z.mul(a3.x).mul(db).neg());

    //  ---- Combine: t0+t2, positive first → no commute ----
    T::axiom_add_congruence_left(t0, a2.x.mul(a3.z).mul(db), t2);
    additive_group_lemmas::lemma_add_congruence_right(
        a2.x.mul(a3.z).mul(db), t2, a2.z.mul(a3.x).mul(db).neg());
    T::axiom_eqv_transitive(t0.add(t2),
        a2.x.mul(a3.z).mul(db).add(t2),
        a2.x.mul(a3.z).mul(db).add(a2.z.mul(a3.x).mul(db).neg()));

    let p = a2.x.mul(a3.z);
    let q = a2.z.mul(a3.x);
    T::axiom_sub_is_add_neg(p.mul(db), q.mul(db));
    T::axiom_eqv_symmetric(
        p.mul(db).sub(q.mul(db)), p.mul(db).add(q.mul(db).neg()));
    ring_lemmas::lemma_sub_mul_right(p, q, db);
    T::axiom_eqv_symmetric(p.sub(q).mul(db), p.mul(db).sub(q.mul(db)));
    T::axiom_eqv_transitive(
        p.mul(db).add(q.mul(db).neg()),
        p.mul(db).sub(q.mul(db)),
        p.sub(q).mul(db));
    T::axiom_eqv_transitive(t0.add(t2),
        p.mul(db).add(q.mul(db).neg()),
        p.sub(q).mul(db));

    //  p.sub(q) ≡ cross.y.neg() via neg_sub
    let cx = cross(drop_w(a2), drop_w(a3));
    lemma_neg_sub(q, p);
    T::axiom_eqv_symmetric(q.sub(p).neg(), p.sub(q));
    T::axiom_mul_congruence_left(p.sub(q), cx.y.neg(), db);
    T::axiom_eqv_transitive(t0.add(t2), p.sub(q).mul(db), cx.y.neg().mul(db));
    ring_lemmas::lemma_mul_neg_left(cx.y, db);
    T::axiom_eqv_transitive(t0.add(t2), cx.y.neg().mul(db), cx.y.mul(db).neg());

    //  Final chain
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b1, row2: ab.row2, row3: ab.row3 }),
        t0.add(t2), cx.y.mul(db).neg());
}

///  Branch 3 (col3): det(b3, b2, ABr2, ABr3) ≡ cross(drop_w(a2),drop_w(a3)).z.mul(db).neg()
proof fn lemma_col3_branch3<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row3, row1: b.row2,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cross(drop_w(a.row2), drop_w(a.row3)).z.mul(det(b)).neg()),
{
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let a2 = a.row2;
    let a3 = a.row3;
    let ab = mat_mul(a, b);
    let db = det(b);

    //  ---- Expand row 2 (ABr2) ----
    lemma_det_expand_third_row_4(b3, b2,
        a2.x, b0, a2.y, b1, a2.z, b2, a2.w, b3, ab.row3);

    //  Kill terms 2 (row12: b2=b2), 3 (row02: b3=b3)
    lemma_det_zero_repeated_row_12(b3, b2, ab.row3);
    lemma_det_zero_repeated_row_02(b3, b2, ab.row3);
    lemma_mul_zero_by_eqv(a2.z,
        det(Mat4x4 { row0: b3, row1: b2, row2: b2, row3: ab.row3 }));
    lemma_mul_zero_by_eqv(a2.w,
        det(Mat4x4 { row0: b3, row1: b2, row2: b3, row3: ab.row3 }));

    let (t0, t1, t2, t3) = (
        a2.x.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: ab.row3 })),
        a2.y.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b1, row3: ab.row3 })),
        a2.z.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b2, row3: ab.row3 })),
        a2.w.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b3, row3: ab.row3 })),
    );
    lemma_sum4_kill_third_fourth(t0, t1, t2, t3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b2, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1).add(t2).add(t3), t0.add(t1));

    //  ---- Sub-branch 3a: det(b3,b2,b0,ABr3) → a3.y * (-db) ----
    lemma_det_expand_fourth_row_4(b3, b2, b0,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_23(b3, b2, b0);
    lemma_det_zero_repeated_row_13(b3, b2, b0);
    lemma_det_zero_repeated_row_03(b3, b2, b0);
    lemma_mul_zero_by_eqv(a3.x,
        det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: b0 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: b2 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: b3 }));
    let (u0, u1, u2, u3) = (
        a3.x.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: b3 })),
    );
    lemma_sum4_kill_first_third_fourth(u0, u1, u2, u3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: ab.row3 }),
        u0.add(u1).add(u2).add(u3),
        a3.y.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: b1 })));

    //  det(b3,b2,b0,b1) ≡ -db by 3 swaps: swap_12(b), swap_23, swap_02
    lemma_det_swap_rows_12(b);
    let m_s1 = Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b3 };
    lemma_det_swap_rows_23(m_s1);
    additive_group_lemmas::lemma_neg_congruence(det(m_s1), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m_s1).neg(), db.neg().neg(), db);
    let d_s2 = det(Mat4x4 { row0: b0, row1: b2, row2: b3, row3: b1 });
    T::axiom_eqv_transitive(d_s2, det(m_s1).neg(), db);
    let m_s2 = Mat4x4 { row0: b0, row1: b2, row2: b3, row3: b1 };
    lemma_det_swap_rows_02(m_s2);
    additive_group_lemmas::lemma_neg_congruence(d_s2, db);
    let d_3a = det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: b1 });
    T::axiom_eqv_transitive(d_3a, d_s2.neg(), db.neg());

    ring_lemmas::lemma_mul_congruence_right(a3.y, d_3a, db.neg());
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: ab.row3 }),
        a3.y.mul(d_3a), a3.y.mul(db.neg()));
    ring_lemmas::lemma_mul_neg_right(a3.y, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: ab.row3 }),
        a3.y.mul(db.neg()), a3.y.mul(db).neg());

    //  t0 ≡ a2.x * (-(a3.y*db)) ≡ -((a2.x*a3.y)*db)
    ring_lemmas::lemma_mul_congruence_right(a2.x,
        det(Mat4x4 { row0: b3, row1: b2, row2: b0, row3: ab.row3 }),
        a3.y.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a2.x, a3.y.mul(db));
    T::axiom_eqv_transitive(t0, a2.x.mul(a3.y.mul(db).neg()), a2.x.mul(a3.y.mul(db)).neg());
    T::axiom_mul_associative(a2.x, a3.y, db);
    T::axiom_eqv_symmetric(a2.x.mul(a3.y).mul(db), a2.x.mul(a3.y.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a2.x.mul(a3.y.mul(db)), a2.x.mul(a3.y).mul(db));
    T::axiom_eqv_transitive(t0, a2.x.mul(a3.y.mul(db)).neg(), a2.x.mul(a3.y).mul(db).neg());

    //  ---- Sub-branch 3b: det(b3,b2,b1,ABr3) → a3.x * db ----
    lemma_det_expand_fourth_row_4(b3, b2, b1,
        a3.x, b0, a3.y, b1, a3.z, b2, a3.w, b3);
    lemma_det_zero_repeated_row_23(b3, b2, b1);
    lemma_det_zero_repeated_row_13(b3, b2, b1);
    lemma_det_zero_repeated_row_03(b3, b2, b1);
    lemma_mul_zero_by_eqv(a3.y,
        det(Mat4x4 { row0: b3, row1: b2, row2: b1, row3: b1 }));
    lemma_mul_zero_by_eqv(a3.z,
        det(Mat4x4 { row0: b3, row1: b2, row2: b1, row3: b2 }));
    lemma_mul_zero_by_eqv(a3.w,
        det(Mat4x4 { row0: b3, row1: b2, row2: b1, row3: b3 }));
    let (v0, v1, v2, v3) = (
        a3.x.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b1, row3: b0 })),
        a3.y.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b1, row3: b1 })),
        a3.z.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b1, row3: b2 })),
        a3.w.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b1, row3: b3 })),
    );
    lemma_sum4_kill_second_third_fourth(v0, v1, v2, v3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b2, row2: b1, row3: ab.row3 }),
        v0.add(v1).add(v2).add(v3),
        a3.x.mul(det(Mat4x4 { row0: b3, row1: b2, row2: b1, row3: b0 })));

    //  det(b3,b2,b1,b0) ≡ db by 2 swaps: swap_12(b) then swap_03
    lemma_det_swap_rows_12(b);
    let m_3b = Mat4x4 { row0: b0, row1: b2, row2: b1, row3: b3 };
    lemma_det_swap_rows_03(m_3b);
    additive_group_lemmas::lemma_neg_congruence(det(m_3b), db.neg());
    additive_group_lemmas::lemma_neg_involution(db);
    T::axiom_eqv_transitive(det(m_3b).neg(), db.neg().neg(), db);
    let d_3b = det(Mat4x4 { row0: b3, row1: b2, row2: b1, row3: b0 });
    T::axiom_eqv_transitive(d_3b, det(m_3b).neg(), db);

    ring_lemmas::lemma_mul_congruence_right(a3.x, d_3b, db);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b2, row2: b1, row3: ab.row3 }),
        a3.x.mul(d_3b), a3.x.mul(db));

    //  t1 ≡ a2.y * (a3.x * db) ≡ (a2.y*a3.x)*db
    ring_lemmas::lemma_mul_congruence_right(a2.y,
        det(Mat4x4 { row0: b3, row1: b2, row2: b1, row3: ab.row3 }),
        a3.x.mul(db));
    T::axiom_mul_associative(a2.y, a3.x, db);
    T::axiom_eqv_symmetric(a2.y.mul(a3.x).mul(db), a2.y.mul(a3.x.mul(db)));
    T::axiom_eqv_transitive(t1, a2.y.mul(a3.x.mul(db)), a2.y.mul(a3.x).mul(db));

    //  ---- Combine: t0+t1, negative first → commute then factor ----
    T::axiom_add_congruence_left(t0, a2.x.mul(a3.y).mul(db).neg(), t1);
    additive_group_lemmas::lemma_add_congruence_right(
        a2.x.mul(a3.y).mul(db).neg(), t1, a2.y.mul(a3.x).mul(db));
    T::axiom_eqv_transitive(t0.add(t1),
        a2.x.mul(a3.y).mul(db).neg().add(t1),
        a2.x.mul(a3.y).mul(db).neg().add(a2.y.mul(a3.x).mul(db)));

    let p = a2.y.mul(a3.x);
    let q = a2.x.mul(a3.y);
    T::axiom_add_commutative(q.mul(db).neg(), p.mul(db));
    T::axiom_eqv_transitive(t0.add(t1),
        q.mul(db).neg().add(p.mul(db)),
        p.mul(db).add(q.mul(db).neg()));

    T::axiom_sub_is_add_neg(p.mul(db), q.mul(db));
    T::axiom_eqv_symmetric(
        p.mul(db).sub(q.mul(db)), p.mul(db).add(q.mul(db).neg()));
    ring_lemmas::lemma_sub_mul_right(p, q, db);
    T::axiom_eqv_symmetric(p.sub(q).mul(db), p.mul(db).sub(q.mul(db)));
    T::axiom_eqv_transitive(
        p.mul(db).add(q.mul(db).neg()),
        p.mul(db).sub(q.mul(db)),
        p.sub(q).mul(db));
    T::axiom_eqv_transitive(t0.add(t1),
        p.mul(db).add(q.mul(db).neg()),
        p.sub(q).mul(db));

    //  p.sub(q) ≡ cross.z.neg() via neg_sub
    let cx = cross(drop_w(a2), drop_w(a3));
    lemma_neg_sub(q, p);
    T::axiom_eqv_symmetric(q.sub(p).neg(), p.sub(q));
    T::axiom_mul_congruence_left(p.sub(q), cx.z.neg(), db);
    T::axiom_eqv_transitive(t0.add(t1), p.sub(q).mul(db), cx.z.neg().mul(db));
    ring_lemmas::lemma_mul_neg_left(cx.z, db);
    T::axiom_eqv_transitive(t0.add(t1), cx.z.neg().mul(db), cx.z.mul(db).neg());

    //  Final chain
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: b2, row2: ab.row2, row3: ab.row3 }),
        t0.add(t1), cx.z.mul(db).neg());
}

//  ===========================================================================
//  Section 10: Col3 main (negative sign, like col1)
//  ===========================================================================

pub proof fn lemma_det_mul_col3<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: b.row3, row1: mat_mul(a,b).row1,
                     row2: mat_mul(a,b).row2, row3: mat_mul(a,b).row3 })
        .eqv(cofactor_vec(a.row1, a.row2, a.row3).w.mul(det(b))),
{
    let a1 = a.row1;
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let ab = mat_mul(a, b);
    let db = det(b);
    let cx = cross(drop_w(a.row2), drop_w(a.row3));

    //  Expand row 1 (ABr1) → 4 terms
    lemma_det_expand_second_row_4(b3,
        a1.x, b0, a1.y, b1, a1.z, b2, a1.w, b3, ab.row2, ab.row3);

    //  Kill fourth (repeated rows 01: b3=b3)
    lemma_det_zero_repeated_row_01(b3, ab.row2, ab.row3);
    lemma_mul_zero_by_eqv(a1.w,
        det(Mat4x4 { row0: b3, row1: b3, row2: ab.row2, row3: ab.row3 }));

    let (e0, e1, e2, e3) = (
        a1.x.mul(det(Mat4x4 { row0: b3, row1: b0, row2: ab.row2, row3: ab.row3 })),
        a1.y.mul(det(Mat4x4 { row0: b3, row1: b1, row2: ab.row2, row3: ab.row3 })),
        a1.z.mul(det(Mat4x4 { row0: b3, row1: b2, row2: ab.row2, row3: ab.row3 })),
        a1.w.mul(det(Mat4x4 { row0: b3, row1: b3, row2: ab.row2, row3: ab.row3 })),
    );
    lemma_sum4_kill_fourth(e0, e1, e2, e3);
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        e0.add(e1).add(e2).add(e3), e0.add(e1).add(e2));

    //  Branch results
    lemma_col3_branch1(a, b);
    lemma_col3_branch2(a, b);
    lemma_col3_branch3(a, b);

    //  Each: a1.i * det(...) ≡ a1.i * (cx.j.mul(db).neg())
    //  → a1.i * (-(cx.j*db)) ≡ -(a1.i * cx.j * db) ≡ -((a1.i*cx.j)*db)
    ring_lemmas::lemma_mul_congruence_right(a1.x,
        det(Mat4x4 { row0: b3, row1: b0, row2: ab.row2, row3: ab.row3 }),
        cx.x.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a1.x, cx.x.mul(db));
    T::axiom_eqv_transitive(e0, a1.x.mul(cx.x.mul(db).neg()), a1.x.mul(cx.x.mul(db)).neg());
    T::axiom_mul_associative(a1.x, cx.x, db);
    T::axiom_eqv_symmetric(a1.x.mul(cx.x).mul(db), a1.x.mul(cx.x.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a1.x.mul(cx.x.mul(db)), a1.x.mul(cx.x).mul(db));
    T::axiom_eqv_transitive(e0, a1.x.mul(cx.x.mul(db)).neg(), a1.x.mul(cx.x).mul(db).neg());

    ring_lemmas::lemma_mul_congruence_right(a1.y,
        det(Mat4x4 { row0: b3, row1: b1, row2: ab.row2, row3: ab.row3 }),
        cx.y.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a1.y, cx.y.mul(db));
    T::axiom_eqv_transitive(e1, a1.y.mul(cx.y.mul(db).neg()), a1.y.mul(cx.y.mul(db)).neg());
    T::axiom_mul_associative(a1.y, cx.y, db);
    T::axiom_eqv_symmetric(a1.y.mul(cx.y).mul(db), a1.y.mul(cx.y.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a1.y.mul(cx.y.mul(db)), a1.y.mul(cx.y).mul(db));
    T::axiom_eqv_transitive(e1, a1.y.mul(cx.y.mul(db)).neg(), a1.y.mul(cx.y).mul(db).neg());

    ring_lemmas::lemma_mul_congruence_right(a1.z,
        det(Mat4x4 { row0: b3, row1: b2, row2: ab.row2, row3: ab.row3 }),
        cx.z.mul(db).neg());
    ring_lemmas::lemma_mul_neg_right(a1.z, cx.z.mul(db));
    T::axiom_eqv_transitive(e2, a1.z.mul(cx.z.mul(db).neg()), a1.z.mul(cx.z.mul(db)).neg());
    T::axiom_mul_associative(a1.z, cx.z, db);
    T::axiom_eqv_symmetric(a1.z.mul(cx.z).mul(db), a1.z.mul(cx.z.mul(db)));
    additive_group_lemmas::lemma_neg_congruence(a1.z.mul(cx.z.mul(db)), a1.z.mul(cx.z).mul(db));
    T::axiom_eqv_transitive(e2, a1.z.mul(cx.z.mul(db)).neg(), a1.z.mul(cx.z).mul(db).neg());

    //  3-sum congruence: e0+e1+e2 ≡ -(A*db) + -(B*db) + -(C*db)
    let aa = a1.x.mul(cx.x);
    let bb = a1.y.mul(cx.y);
    let cc = a1.z.mul(cx.z);
    lemma_add_congruence_3(
        e0, aa.mul(db).neg(),
        e1, bb.mul(db).neg(),
        e2, cc.mul(db).neg());

    //  Pull negation through: -(A*db) + -(B*db) + -(C*db) ≡ -((A*db) + (B*db) + (C*db))
    additive_group_lemmas::lemma_neg_add(aa.mul(db), bb.mul(db));
    T::axiom_eqv_symmetric(
        aa.mul(db).add(bb.mul(db)).neg(),
        aa.mul(db).neg().add(bb.mul(db).neg()));
    T::axiom_add_congruence_left(
        aa.mul(db).neg().add(bb.mul(db).neg()),
        aa.mul(db).add(bb.mul(db)).neg(),
        cc.mul(db).neg());
    additive_group_lemmas::lemma_neg_add(aa.mul(db).add(bb.mul(db)), cc.mul(db));
    T::axiom_eqv_symmetric(
        aa.mul(db).add(bb.mul(db)).add(cc.mul(db)).neg(),
        aa.mul(db).add(bb.mul(db)).neg().add(cc.mul(db).neg()));
    T::axiom_eqv_transitive(
        aa.mul(db).neg().add(bb.mul(db).neg()).add(cc.mul(db).neg()),
        aa.mul(db).add(bb.mul(db)).neg().add(cc.mul(db).neg()),
        aa.mul(db).add(bb.mul(db)).add(cc.mul(db)).neg());

    //  Factor inner: (A*db + B*db + C*db) ≡ (A+B+C)*db
    lemma_factor_3(aa, bb, cc, db);
    additive_group_lemmas::lemma_neg_congruence(
        aa.mul(db).add(bb.mul(db)).add(cc.mul(db)),
        aa.add(bb).add(cc).mul(db));
    T::axiom_eqv_transitive(
        aa.mul(db).neg().add(bb.mul(db).neg()).add(cc.mul(db).neg()),
        aa.mul(db).add(bb.mul(db)).add(cc.mul(db)).neg(),
        aa.add(bb).add(cc).mul(db).neg());

    //  cofactor_vec.w = triple.neg(), so cofactor_vec.w.mul(db) ≡ triple.neg().mul(db) ≡ -(triple*db)
    ring_lemmas::lemma_mul_neg_left(aa.add(bb).add(cc), db);
    T::axiom_eqv_symmetric(
        aa.add(bb).add(cc).neg().mul(db),
        aa.add(bb).add(cc).mul(db).neg());
    T::axiom_eqv_transitive(
        aa.mul(db).neg().add(bb.mul(db).neg()).add(cc.mul(db).neg()),
        aa.add(bb).add(cc).mul(db).neg(),
        cofactor_vec(a1, a.row2, a.row3).w.mul(db));

    //  Chain: det ≡ 3-sum ≡ neg-factored ≡ cofactor_vec.w * db
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        e0.add(e1).add(e2),
        aa.mul(db).neg().add(bb.mul(db).neg()).add(cc.mul(db).neg()));
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: b3, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        aa.mul(db).neg().add(bb.mul(db).neg()).add(cc.mul(db).neg()),
        cofactor_vec(a1, a.row2, a.row3).w.mul(db));
}

//  ===========================================================================
//  Section 11: First-row expansion helper
//  ===========================================================================

///  Expand det when row 0 (first row) is a 4-term scaled sum.
pub proof fn lemma_det_expand_first_row_4<T: Ring>(
    s0: T, v0: Vec4<T>, s1: T, v1: Vec4<T>, s2: T, v2: Vec4<T>, s3: T, v3: Vec4<T>,
    r1: Vec4<T>, r2: Vec4<T>, r3: Vec4<T>,
)
    ensures
        det(Mat4x4 {
            row0: scale(s0, v0).add(scale(s1, v1)).add(scale(s2, v2)).add(scale(s3, v3)),
            row1: r1, row2: r2, row3: r3 }).eqv(
            s0.mul(det(Mat4x4 { row0: v0, row1: r1, row2: r2, row3: r3 }))
              .add(s1.mul(det(Mat4x4 { row0: v1, row1: r1, row2: r2, row3: r3 })))
              .add(s2.mul(det(Mat4x4 { row0: v2, row1: r1, row2: r2, row3: r3 })))
              .add(s3.mul(det(Mat4x4 { row0: v3, row1: r1, row2: r2, row3: r3 })))
        ),
{
    let x = scale(s0, v0);
    let y = scale(s1, v1);
    let z = scale(s2, v2);
    let w = scale(s3, v3);

    //  Linearity: split 3 times
    lemma_det_linear_first_row(x.add(y).add(z), w, r1, r2, r3);
    lemma_det_linear_first_row(x.add(y), z, r1, r2, r3);
    lemma_det_linear_first_row(x, y, r1, r2, r3);

    //  Scale: pull out scalars
    lemma_det_scale_first_row(s0, v0, r1, r2, r3);
    lemma_det_scale_first_row(s1, v1, r1, r2, r3);
    lemma_det_scale_first_row(s2, v2, r1, r2, r3);
    lemma_det_scale_first_row(s3, v3, r1, r2, r3);

    let d0 = det(Mat4x4 { row0: v0, row1: r1, row2: r2, row3: r3 });
    let d1 = det(Mat4x4 { row0: v1, row1: r1, row2: r2, row3: r3 });
    let d2 = det(Mat4x4 { row0: v2, row1: r1, row2: r2, row3: r3 });
    let d3 = det(Mat4x4 { row0: v3, row1: r1, row2: r2, row3: r3 });
    let dx = det(Mat4x4 { row0: x, row1: r1, row2: r2, row3: r3 });
    let dy = det(Mat4x4 { row0: y, row1: r1, row2: r2, row3: r3 });
    let dz = det(Mat4x4 { row0: z, row1: r1, row2: r2, row3: r3 });
    let dw = det(Mat4x4 { row0: w, row1: r1, row2: r2, row3: r3 });

    //  Chain inner pair: dx + dy ≡ s0*d0 + s1*d1
    T::axiom_add_congruence_left(dx, s0.mul(d0), dy);
    additive_group_lemmas::lemma_add_congruence_right(s0.mul(d0), dy, s1.mul(d1));
    T::axiom_eqv_transitive(dx.add(dy), s0.mul(d0).add(dy), s0.mul(d0).add(s1.mul(d1)));

    let dxy = det(Mat4x4 { row0: x.add(y), row1: r1, row2: r2, row3: r3 });
    T::axiom_eqv_transitive(dxy, dx.add(dy), s0.mul(d0).add(s1.mul(d1)));

    //  dxy + dz ≡ (s0*d0+s1*d1) + s2*d2
    T::axiom_add_congruence_left(dxy, s0.mul(d0).add(s1.mul(d1)), dz);
    additive_group_lemmas::lemma_add_congruence_right(
        s0.mul(d0).add(s1.mul(d1)), dz, s2.mul(d2));
    T::axiom_eqv_transitive(dxy.add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)));

    let dxyz = det(Mat4x4 { row0: x.add(y).add(z), row1: r1, row2: r2, row3: r3 });
    T::axiom_eqv_transitive(dxyz, dxy.add(dz),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)));

    //  dxyz + dw ≡ final 4-term sum
    T::axiom_add_congruence_left(dxyz,
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)), dw);
    additive_group_lemmas::lemma_add_congruence_right(
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)), dw, s3.mul(d3));
    T::axiom_eqv_transitive(dxyz.add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(s3.mul(d3)));

    let dxyzw = det(Mat4x4 { row0: x.add(y).add(z).add(w), row1: r1, row2: r2, row3: r3 });
    T::axiom_eqv_transitive(dxyzw, dxyz.add(dw),
        s0.mul(d0).add(s1.mul(d1)).add(s2.mul(d2)).add(s3.mul(d3)));
}

//  ===========================================================================
//  Section 12: Main orchestrator — det(AB) ≡ det(A) * det(B)
//  ===========================================================================

pub proof fn lemma_det_multiplicative<T: Ring>(a: Mat4x4<T>, b: Mat4x4<T>)
    ensures det(mat_mul(a, b)).eqv(det(a).mul(det(b))),
{
    let a0 = a.row0;
    let (b0, b1, b2, b3) = (b.row0, b.row1, b.row2, b.row3);
    let ab = mat_mul(a, b);
    let db = det(b);
    let cv = cofactor_vec(a.row1, a.row2, a.row3);

    //  Phase 1: det(AB) ≡ Σ a0.i * det(bi, ABr1, ABr2, ABr3)
    //  ABr0 = scale(a0.x, b0) + scale(a0.y, b1) + scale(a0.z, b2) + scale(a0.w, b3)
    lemma_det_expand_first_row_4(
        a0.x, b0, a0.y, b1, a0.z, b2, a0.w, b3,
        ab.row1, ab.row2, ab.row3);

    //  Phase 2: Per-column results
    lemma_det_mul_col0(a, b); //  det(b0, ABr1, ABr2, ABr3) ≡ cv.x * db
    lemma_det_mul_col1(a, b); //  det(b1, ABr1, ABr2, ABr3) ≡ cv.y * db
    lemma_det_mul_col2(a, b); //  det(b2, ABr1, ABr2, ABr3) ≡ cv.z * db
    lemma_det_mul_col3(a, b); //  det(b3, ABr1, ABr2, ABr3) ≡ cv.w * db

    //  Phase 3: Scale — a0.i * (cv.i * db) ≡ (a0.i * cv.i) * db
    ring_lemmas::lemma_mul_congruence_right(a0.x,
        det(Mat4x4 { row0: b0, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        cv.x.mul(db));
    T::axiom_mul_associative(a0.x, cv.x, db);
    T::axiom_eqv_symmetric(a0.x.mul(cv.x).mul(db), a0.x.mul(cv.x.mul(db)));
    T::axiom_eqv_transitive(
        a0.x.mul(det(Mat4x4 { row0: b0, row1: ab.row1, row2: ab.row2, row3: ab.row3 })),
        a0.x.mul(cv.x.mul(db)), a0.x.mul(cv.x).mul(db));

    ring_lemmas::lemma_mul_congruence_right(a0.y,
        det(Mat4x4 { row0: b1, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        cv.y.mul(db));
    T::axiom_mul_associative(a0.y, cv.y, db);
    T::axiom_eqv_symmetric(a0.y.mul(cv.y).mul(db), a0.y.mul(cv.y.mul(db)));
    T::axiom_eqv_transitive(
        a0.y.mul(det(Mat4x4 { row0: b1, row1: ab.row1, row2: ab.row2, row3: ab.row3 })),
        a0.y.mul(cv.y.mul(db)), a0.y.mul(cv.y).mul(db));

    ring_lemmas::lemma_mul_congruence_right(a0.z,
        det(Mat4x4 { row0: b2, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        cv.z.mul(db));
    T::axiom_mul_associative(a0.z, cv.z, db);
    T::axiom_eqv_symmetric(a0.z.mul(cv.z).mul(db), a0.z.mul(cv.z.mul(db)));
    T::axiom_eqv_transitive(
        a0.z.mul(det(Mat4x4 { row0: b2, row1: ab.row1, row2: ab.row2, row3: ab.row3 })),
        a0.z.mul(cv.z.mul(db)), a0.z.mul(cv.z).mul(db));

    ring_lemmas::lemma_mul_congruence_right(a0.w,
        det(Mat4x4 { row0: b3, row1: ab.row1, row2: ab.row2, row3: ab.row3 }),
        cv.w.mul(db));
    T::axiom_mul_associative(a0.w, cv.w, db);
    T::axiom_eqv_symmetric(a0.w.mul(cv.w).mul(db), a0.w.mul(cv.w.mul(db)));
    T::axiom_eqv_transitive(
        a0.w.mul(det(Mat4x4 { row0: b3, row1: ab.row1, row2: ab.row2, row3: ab.row3 })),
        a0.w.mul(cv.w.mul(db)), a0.w.mul(cv.w).mul(db));

    //  Phase 4: 4-sum congruence
    lemma_add_congruence_4(
        a0.x.mul(det(Mat4x4 { row0: b0, row1: ab.row1, row2: ab.row2, row3: ab.row3 })),
        a0.x.mul(cv.x).mul(db),
        a0.y.mul(det(Mat4x4 { row0: b1, row1: ab.row1, row2: ab.row2, row3: ab.row3 })),
        a0.y.mul(cv.y).mul(db),
        a0.z.mul(det(Mat4x4 { row0: b2, row1: ab.row1, row2: ab.row2, row3: ab.row3 })),
        a0.z.mul(cv.z).mul(db),
        a0.w.mul(det(Mat4x4 { row0: b3, row1: ab.row1, row2: ab.row2, row3: ab.row3 })),
        a0.w.mul(cv.w).mul(db));

    //  Phase 5: Factor out db
    lemma_factor_4(a0.x.mul(cv.x), a0.y.mul(cv.y), a0.z.mul(cv.z), a0.w.mul(cv.w), db);
    //  (a0.x*cv.x + a0.y*cv.y + a0.z*cv.z + a0.w*cv.w) = dot(a0, cv) definitionally
    //  dot(a0, cv) * db = det(a) * det(b) via det_as_dot

    //  Phase 6: Chain everything
    let sum_orig =
        a0.x.mul(det(Mat4x4 { row0: b0, row1: ab.row1, row2: ab.row2, row3: ab.row3 }))
        .add(a0.y.mul(det(Mat4x4 { row0: b1, row1: ab.row1, row2: ab.row2, row3: ab.row3 })))
        .add(a0.z.mul(det(Mat4x4 { row0: b2, row1: ab.row1, row2: ab.row2, row3: ab.row3 })))
        .add(a0.w.mul(det(Mat4x4 { row0: b3, row1: ab.row1, row2: ab.row2, row3: ab.row3 })));
    let sum_factored =
        a0.x.mul(cv.x).mul(db)
        .add(a0.y.mul(cv.y).mul(db))
        .add(a0.z.mul(cv.z).mul(db))
        .add(a0.w.mul(cv.w).mul(db));

    //  det(AB) ≡ sum_orig ≡ sum_factored ≡ dot(a0,cv)*db
    T::axiom_eqv_transitive(det(ab), sum_orig, sum_factored);
    T::axiom_eqv_transitive(det(ab), sum_factored, dot(a0, cv).mul(db));

    //  dot(a0, cv) ≡ det(a) via det_as_dot
    lemma_det_as_dot(a);
    T::axiom_eqv_symmetric(det(a), dot(a0, cv));
    T::axiom_mul_congruence_left(dot(a0, cv), det(a), db);
    T::axiom_eqv_transitive(det(ab), dot(a0, cv).mul(db), det(a).mul(db));
}

} //  verus!
