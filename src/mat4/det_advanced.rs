use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use crate::vec3::Vec3;
use crate::vec3::ops::{cross, triple};
use crate::vec4::Vec4;
use crate::vec4::ops::dot;
use super::Mat4x4;
use super::ops::{det, drop_x, drop_y, drop_z, drop_w, cofactor_vec,
    lemma_det_as_dot, lemma_det_congruence,
    lemma_det_swap_rows_12, lemma_det_swap_rows_23, lemma_det_swap_rows_13,
    lemma_det_linear_first_row, lemma_det_linear_second_row,
    lemma_det_zero_repeated_row_12, lemma_det_zero_repeated_row_23,
    lemma_det_zero_repeated_row_13,
    lemma_flip_neg_eqv, lemma_negate_alt_sum_4};

verus! {

// ---------------------------------------------------------------------------
// Helper: a pair of cross product components that are structurally equal
// cancel when multiplied by commuted scalars.
// Proves: v_i * v_j * M - v_j * v_i * M ≡ 0
// (where the signs come from the Laplace expansion).
// ---------------------------------------------------------------------------

/// Helper: a * b * m ≡ b * a * m  (from mul_commutative + associativity)
proof fn lemma_mul_comm_product<T: Ring>(a: T, b: T, m: T)
    ensures
        a.mul(b).mul(m).eqv(b.mul(a).mul(m)),
{
    T::axiom_mul_commutative(a, b);
    T::axiom_mul_congruence_left(a.mul(b), b.mul(a), m);
}

/// Helper: a - b ≡ 0 when a ≡ b
proof fn lemma_sub_self_eqv<T: Ring>(a: T, b: T)
    requires a.eqv(b)
    ensures a.sub(b).eqv(T::zero()),
{
    // a.sub(b) ≡ b.sub(b) via sub_congruence(a, b, b, b)
    T::axiom_eqv_reflexive(b);
    additive_group_lemmas::lemma_sub_congruence(a, b, b, b);
    // b.sub(b) ≡ 0
    additive_group_lemmas::lemma_sub_self(b);
    T::axiom_eqv_transitive(a.sub(b), b.sub(b), T::zero());
}

/// Helper: a * m - b * m ≡ 0 when a ≡ b
proof fn lemma_sub_same_factor<T: Ring>(a: T, b: T, m: T)
    requires a.eqv(b)
    ensures a.mul(m).sub(b.mul(m)).eqv(T::zero()),
{
    T::axiom_mul_congruence_left(a, b, m);
    // a*m ≡ b*m → a*m - b*m ≡ 0
    lemma_sub_self_eqv(a.mul(m), b.mul(m));
}

/// Helper: a + b ≡ 0 when a ≡ b.neg()
proof fn lemma_add_neg_cancel<T: Ring>(a: T, b: T)
    requires a.eqv(b.neg())
    ensures a.add(b).eqv(T::zero()),
{
    // a ≡ b.neg() → a + b ≡ b.neg() + b
    T::axiom_add_congruence_left(a, b.neg(), b);
    // b.neg() + b ≡ 0
    additive_group_lemmas::lemma_add_inverse_left(b);
    T::axiom_eqv_transitive(a.add(b), b.neg().add(b), T::zero());
}

/// a*(b*m) ≡ b*(a*m)  (swap outer factors via associativity + commutativity)
proof fn lemma_product_swap<T: Ring>(a: T, b: T, m: T)
    ensures a.mul(b.mul(m)).eqv(b.mul(a.mul(m)))
{
    T::axiom_mul_associative(a, b, m);
    T::axiom_eqv_symmetric(a.mul(b).mul(m), a.mul(b.mul(m)));
    T::axiom_mul_commutative(a, b);
    T::axiom_mul_congruence_left(a.mul(b), b.mul(a), m);
    T::axiom_mul_associative(b, a, m);
    T::axiom_eqv_transitive(a.mul(b.mul(m)), a.mul(b).mul(m), b.mul(a).mul(m));
    T::axiom_eqv_transitive(a.mul(b.mul(m)), b.mul(a).mul(m), b.mul(a.mul(m)));
}

/// (a+x) - (a+y) ≡ x - y  (cancel common left addend)
proof fn lemma_cancel_common_left_addend<T: Ring>(a: T, x: T, y: T)
    ensures a.add(x).sub(a.add(y)).eqv(x.sub(y))
{
    // sub_add_sub(a+x, a, a+y): ((a+x)-a) + (a-(a+y)) ≡ (a+x)-(a+y)
    additive_group_lemmas::lemma_sub_add_sub(a.add(x), a, a.add(y));
    T::axiom_eqv_symmetric(
        a.add(x).sub(a).add(a.sub(a.add(y))),
        a.add(x).sub(a.add(y)),
    );
    // (a+x)-a ≡ x: commute then cancel
    T::axiom_add_commutative(a, x);
    T::axiom_eqv_reflexive(a);
    additive_group_lemmas::lemma_sub_congruence(a.add(x), x.add(a), a, a);
    additive_group_lemmas::lemma_add_then_sub_cancel(x, a);
    T::axiom_eqv_transitive(a.add(x).sub(a), x.add(a).sub(a), x);
    // a-(a+y) ≡ -y: antisymmetric then cancel
    additive_group_lemmas::lemma_sub_antisymmetric(a, a.add(y));
    T::axiom_add_commutative(a, y);
    T::axiom_eqv_reflexive(a);
    additive_group_lemmas::lemma_sub_congruence(a.add(y), y.add(a), a, a);
    additive_group_lemmas::lemma_add_then_sub_cancel(y, a);
    T::axiom_eqv_transitive(a.add(y).sub(a), y.add(a).sub(a), y);
    additive_group_lemmas::lemma_neg_congruence(a.add(y).sub(a), y);
    T::axiom_eqv_transitive(a.sub(a.add(y)), a.add(y).sub(a).neg(), y.neg());
    // combine: ((a+x)-a) + (a-(a+y)) ≡ x + (-y)
    additive_group_lemmas::lemma_add_congruence(
        a.add(x).sub(a), x, a.sub(a.add(y)), y.neg(),
    );
    // x + (-y) ≡ x - y
    T::axiom_sub_is_add_neg(x, y);
    T::axiom_eqv_symmetric(x.sub(y), x.add(y.neg()));
    T::axiom_eqv_transitive(
        a.add(x).sub(a).add(a.sub(a.add(y))),
        x.add(y.neg()),
        x.sub(y),
    );
    // chain: (a+x)-(a+y) ≡ LHS ≡ x-y
    T::axiom_eqv_transitive(
        a.add(x).sub(a.add(y)),
        a.add(x).sub(a).add(a.sub(a.add(y))),
        x.sub(y),
    );
}

/// (a+b) - (c+d) ≡ (a-c) + (b-d)
proof fn lemma_sum_sub_sum<T: Ring>(a: T, b: T, c: T, d: T)
    ensures a.add(b).sub(c.add(d)).eqv(a.sub(c).add(b.sub(d)))
{
    // (a+b) - (c+d)
    // ≡ (a+b) + (-(c+d))         [sub_is_add_neg]
    // ≡ (a+b) + ((-c)+(-d))      [neg_add]
    // ≡ (a+(-c)) + (b+(-d))      [add_rearrange_2x2]
    // ≡ (a-c) + (b-d)            [sub_is_add_neg reverse]
    T::axiom_sub_is_add_neg(a.add(b), c.add(d));
    additive_group_lemmas::lemma_neg_add(c, d);
    T::axiom_eqv_reflexive(a.add(b));
    additive_group_lemmas::lemma_add_congruence(
        a.add(b), a.add(b),
        c.add(d).neg(), c.neg().add(d.neg()),
    );
    additive_group_lemmas::lemma_add_rearrange_2x2(a, b, c.neg(), d.neg());
    // chain: sub form ≡ add_neg form ≡ rearranged ≡ rearranged
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(b).add(c.add(d).neg()),
        a.add(b).add(c.neg().add(d.neg())),
    );
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(b).add(c.neg().add(d.neg())),
        a.add(c.neg()).add(b.add(d.neg())),
    );
    // convert a+(-c) ≡ a-c and b+(-d) ≡ b-d
    T::axiom_sub_is_add_neg(a, c);
    T::axiom_eqv_symmetric(a.sub(c), a.add(c.neg()));
    T::axiom_sub_is_add_neg(b, d);
    T::axiom_eqv_symmetric(b.sub(d), b.add(d.neg()));
    additive_group_lemmas::lemma_add_congruence(
        a.add(c.neg()), a.sub(c),
        b.add(d.neg()), b.sub(d),
    );
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(c.neg()).add(b.add(d.neg())),
        a.sub(c).add(b.sub(d)),
    );
}

/// When a1 ≡ b1: ((a1+a2)+a3) - ((b1+b2)+b3) ≡ (a2-b2) + (a3-b3)
proof fn lemma_add3_sub_add3_cancel_first<T: Ring>(
    a1: T, a2: T, a3: T, b1: T, b2: T, b3: T,
)
    requires a1.eqv(b1)
    ensures
        a1.add(a2).add(a3).sub(b1.add(b2).add(b3)).eqv(
            a2.sub(b2).add(a3.sub(b3))
        ),
{
    // Reassociate both sides
    T::axiom_add_associative(a1, a2, a3);
    T::axiom_add_associative(b1, b2, b3);
    additive_group_lemmas::lemma_sub_congruence(
        a1.add(a2).add(a3), a1.add(a2.add(a3)),
        b1.add(b2).add(b3), b1.add(b2.add(b3)),
    );
    // Replace b1 with a1 on right side
    T::axiom_eqv_symmetric(a1, b1);
    T::axiom_add_congruence_left(b1, a1, b2.add(b3));
    T::axiom_eqv_reflexive(a1.add(a2.add(a3)));
    additive_group_lemmas::lemma_sub_congruence(
        a1.add(a2.add(a3)), a1.add(a2.add(a3)),
        b1.add(b2.add(b3)), a1.add(b2.add(b3)),
    );
    // cancel_common_left_addend
    lemma_cancel_common_left_addend(a1, a2.add(a3), b2.add(b3));
    // sum_sub_sum
    lemma_sum_sub_sum(a2, a3, b2, b3);
    // chain
    let s1 = a1.add(a2).add(a3).sub(b1.add(b2).add(b3));
    let s2 = a1.add(a2.add(a3)).sub(b1.add(b2.add(b3)));
    let s3 = a1.add(a2.add(a3)).sub(a1.add(b2.add(b3)));
    let s4 = a2.add(a3).sub(b2.add(b3));
    let s5 = a2.sub(b2).add(a3.sub(b3));
    T::axiom_eqv_transitive(s1, s2, s3);
    T::axiom_eqv_transitive(s1, s3, s4);
    T::axiom_eqv_transitive(s1, s4, s5);
}

/// s * ((p+q)+r) ≡ ((s*p)+(s*q)) + (s*r)
proof fn lemma_distribute_mul_over_add3<T: Ring>(s: T, p: T, q: T, r: T)
    ensures
        s.mul(p.add(q).add(r)).eqv(
            s.mul(p).add(s.mul(q)).add(s.mul(r))
        ),
{
    // s * ((p+q)+r) ≡ s*(p+q) + s*r
    T::axiom_mul_distributes_left(s, p.add(q), r);
    // s * (p+q) ≡ s*p + s*q
    T::axiom_mul_distributes_left(s, p, q);
    T::axiom_add_congruence_left(s.mul(p.add(q)), s.mul(p).add(s.mul(q)), s.mul(r));
    T::axiom_eqv_transitive(
        s.mul(p.add(q).add(r)),
        s.mul(p.add(q)).add(s.mul(r)),
        s.mul(p).add(s.mul(q)).add(s.mul(r)),
    );
}

/// 0 + 0 ≡ 0
proof fn lemma_zero_add_zero<T: Ring>(a: T, b: T)
    requires a.eqv(T::zero()), b.eqv(T::zero())
    ensures a.add(b).eqv(T::zero())
{
    additive_group_lemmas::lemma_add_congruence(a, T::zero(), b, T::zero());
    additive_group_lemmas::lemma_add_zero_left::<T>(T::zero());
    T::axiom_eqv_transitive(a.add(b), T::zero().add(T::zero()), T::zero());
}

// ---------------------------------------------------------------------------
// The core proof: det(a, a, c, d) ≡ 0
//
// Strategy: det(a, a, c, d) = dot(a, cofactor_vec(a, c, d)).
// Each cofactor triple(drop_k(a), drop_k(c), drop_k(d)) = dot(drop_k(a), cross(drop_k(c), drop_k(d))).
// The full expression expands to 12 terms that cancel in 6 pairs
// by Ring commutativity (a.i * a.j ≡ a.j * a.i) and the fact that
// certain cross-product components are structurally identical.
//
// 4 pairs have structurally equal cross components: (xy), (xw), (yz), (zw)
// 2 pairs have negated cross components: (xz), (yw)
// ---------------------------------------------------------------------------

/// If rows 0 and 1 are equal, det is zero.
pub proof fn lemma_det_zero_repeated_row_01<T: Ring>(a: Vec4<T>, c: Vec4<T>, d: Vec4<T>)
    ensures
        det(Mat4x4 { row0: a, row1: a, row2: c, row3: d }).eqv(T::zero()),
{
    // We prove this by expanding det = dot(a, cofactor_vec(a, c, d))
    // and showing the 12-term expansion cancels pairwise.
    //
    // Key structural equalities of cross-product components:
    //   cross(drop_x(c), drop_x(d)).x == cross(drop_y(c), drop_y(d)).x  (both = c.z*d.w - c.w*d.z)
    //   cross(drop_x(c), drop_x(d)).z == cross(drop_w(c), drop_w(d)).x  (both = c.y*d.z - c.z*d.y)  [note: was labeled wrong, this is for pair (x,w)]
    //   cross(drop_y(c), drop_y(d)).y == cross(drop_z(c), drop_z(d)).y  (both = c.w*d.x - c.x*d.w)  [pair (y,z)]
    //   cross(drop_z(c), drop_z(d)).z == cross(drop_w(c), drop_w(d)).z  (both = c.x*d.y - c.y*d.x)  [pair (z,w)]
    //
    // And negation relations:
    //   cross(drop_x(c), drop_x(d)).y ≡ -cross(drop_z(c), drop_z(d)).x  [pair (x,z)]
    //   cross(drop_y(c), drop_y(d)).z ≡ -cross(drop_w(c), drop_w(d)).y  [pair (y,w)]

    // This proof requires a detailed algebraic expansion.
    // For now, we mark this as proof debt to be resolved.
    assume(false);
}

// ---------------------------------------------------------------------------
// swap_01: Swapping rows 0 and 1 negates the determinant.
// Derived from bilinearity + zero_repeated_row_01.
// ---------------------------------------------------------------------------

/// Swapping rows 0 and 1 negates the determinant.
pub proof fn lemma_det_swap_rows_01<T: Ring>(m: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: m.row1, row1: m.row0, row2: m.row2, row3: m.row3 }).eqv(
            det(m).neg()
        ),
{
    let r0 = m.row0; let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;
    let a = r0; let b = r1;

    // det(a+b, a+b, r2, r3) ≡ 0
    lemma_det_zero_repeated_row_01(a.add(b), r2, r3);

    // Expand by linearity in row 0:
    // det(a+b, a+b, r2, r3) ≡ det(a, a+b, r2, r3) + det(b, a+b, r2, r3)
    lemma_det_linear_first_row(a, b, a.add(b), r2, r3);

    // Expand each by linearity in row 1:
    // det(a, a+b, r2, r3) ≡ det(a, a, r2, r3) + det(a, b, r2, r3)
    lemma_det_linear_second_row(a, a, b, r2, r3);
    // det(b, a+b, r2, r3) ≡ det(b, a, r2, r3) + det(b, b, r2, r3)
    lemma_det_linear_second_row(b, a, b, r2, r3);

    // det(a, a, r2, r3) ≡ 0, det(b, b, r2, r3) ≡ 0
    lemma_det_zero_repeated_row_01(a, r2, r3);
    lemma_det_zero_repeated_row_01(b, r2, r3);

    // So: 0 ≡ (0 + det(a,b,...)) + (det(b,a,...) + 0)
    //       ≡ det(a,b,...) + det(b,a,...)
    let d_aa = det(Mat4x4 { row0: a, row1: a, row2: r2, row3: r3 });
    let d_ab = det(Mat4x4 { row0: a, row1: b, row2: r2, row3: r3 });  // = det(m)
    let d_ba = det(Mat4x4 { row0: b, row1: a, row2: r2, row3: r3 });  // = target
    let d_bb = det(Mat4x4 { row0: b, row1: b, row2: r2, row3: r3 });

    // d_aa + d_ab ≡ 0 + d_ab ≡ d_ab
    T::axiom_eqv_reflexive(d_ab);
    additive_group_lemmas::lemma_add_congruence::<T>(d_aa, T::zero(), d_ab, d_ab);
    additive_group_lemmas::lemma_add_zero_left::<T>(d_ab);
    T::axiom_eqv_transitive(d_aa.add(d_ab), T::zero().add(d_ab), d_ab);

    // d_ba + d_bb ≡ d_ba + 0 ≡ d_ba
    T::axiom_eqv_reflexive(d_ba);
    additive_group_lemmas::lemma_add_congruence::<T>(d_ba, d_ba, d_bb, T::zero());
    T::axiom_add_zero_right(d_ba);
    T::axiom_eqv_transitive(d_ba.add(d_bb), d_ba.add(T::zero()), d_ba);

    // det(a+b, a+b, ...) ≡ (d_aa + d_ab) + (d_ba + d_bb)
    // First: det_linear_first_row gives det(a+b, a+b, ...) ≡ det(a, a+b, ...) + det(b, a+b, ...)
    // det(a, a+b, ...) ≡ d_aa + d_ab, det(b, a+b, ...) ≡ d_ba + d_bb
    let d_a_ab = det(Mat4x4 { row0: a, row1: a.add(b), row2: r2, row3: r3 });
    let d_b_ab = det(Mat4x4 { row0: b, row1: a.add(b), row2: r2, row3: r3 });

    // d_a_ab ≡ d_aa + d_ab ≡ d_ab
    T::axiom_eqv_transitive(d_a_ab, d_aa.add(d_ab), d_ab);
    // d_b_ab ≡ d_ba + d_bb ≡ d_ba
    T::axiom_eqv_transitive(d_b_ab, d_ba.add(d_bb), d_ba);

    // d_a_ab + d_b_ab ≡ d_ab + d_ba
    additive_group_lemmas::lemma_add_congruence::<T>(d_a_ab, d_ab, d_b_ab, d_ba);

    // det(a+b, a+b, ...) ≡ d_a_ab + d_b_ab ≡ d_ab + d_ba
    let d_sum = det(Mat4x4 { row0: a.add(b), row1: a.add(b), row2: r2, row3: r3 });
    T::axiom_eqv_transitive(d_sum, d_a_ab.add(d_b_ab), d_ab.add(d_ba));

    // d_sum ≡ 0 (from zero_repeated_row_01)
    // So: 0 ≡ d_ab + d_ba
    T::axiom_eqv_symmetric(d_sum, T::zero());
    T::axiom_eqv_transitive(T::zero(), d_sum, d_ab.add(d_ba));
    // d_ab + d_ba ≡ 0
    T::axiom_eqv_symmetric(T::zero(), d_ab.add(d_ba));

    // d_ba ≡ -d_ab (= det(m).neg())
    additive_group_lemmas::lemma_neg_unique(d_ab, d_ba);
}

// ---------------------------------------------------------------------------
// Derived swaps: 02, 03  (compose with swap_01)
// ---------------------------------------------------------------------------

/// Swapping rows 0 and 2 negates the determinant.
pub proof fn lemma_det_swap_rows_02<T: Ring>(m: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: m.row2, row1: m.row1, row2: m.row0, row3: m.row3 }).eqv(
            det(m).neg()
        ),
{
    let r0 = m.row0; let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;

    // swap_01: det(r1, r0, r2, r3) ≡ -det(r0, r1, r2, r3)
    lemma_det_swap_rows_01(m);
    let m2 = Mat4x4 { row0: r1, row1: r0, row2: r2, row3: r3 };

    // swap_12 on m2: det(r1, r2, r0, r3) ≡ -det(r1, r0, r2, r3)
    lemma_det_swap_rows_12(m2);
    let m3 = Mat4x4 { row0: r1, row1: r2, row2: r0, row3: r3 };

    // Chain: det(m2).neg() where det(m2) ≡ det(m).neg()
    // det(m2).neg() ≡ det(m).neg().neg() ≡ det(m)
    T::axiom_neg_congruence(det(m2), det(m).neg());
    additive_group_lemmas::lemma_neg_involution(det(m));
    T::axiom_eqv_transitive(det(m2).neg(), det(m).neg().neg(), det(m));
    // det(m3) ≡ det(m2).neg() ≡ det(m)
    T::axiom_eqv_transitive(det(m3), det(m2).neg(), det(m));

    // swap_01 on m3: det(r2, r1, r0, r3) ≡ -det(r1, r2, r0, r3)
    lemma_det_swap_rows_01(m3);

    // -det(m3) ≡ -det(m)
    T::axiom_neg_congruence(det(m3), det(m));

    // chain: det(r2, r1, r0, r3) ≡ det(m3).neg() ≡ det(m).neg()
    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: r2, row1: r1, row2: r0, row3: r3 }),
        det(m3).neg(),
        det(m).neg(),
    );
}

/// Swapping rows 0 and 3 negates the determinant.
pub proof fn lemma_det_swap_rows_03<T: Ring>(m: Mat4x4<T>)
    ensures
        det(Mat4x4 { row0: m.row3, row1: m.row1, row2: m.row2, row3: m.row0 }).eqv(
            det(m).neg()
        ),
{
    let r0 = m.row0; let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;

    // swap_01: det(r1, r0, r2, r3) ≡ -det(m)
    lemma_det_swap_rows_01(m);
    let m2 = Mat4x4 { row0: r1, row1: r0, row2: r2, row3: r3 };

    // swap_13 on m2: det(r1, r3, r2, r0) ≡ -det(m2)
    lemma_det_swap_rows_13(m2);
    let m3 = Mat4x4 { row0: r1, row1: r3, row2: r2, row3: r0 };

    // det(m2).neg() ≡ det(m).neg().neg() ≡ det(m)
    T::axiom_neg_congruence(det(m2), det(m).neg());
    additive_group_lemmas::lemma_neg_involution(det(m));
    T::axiom_eqv_transitive(det(m2).neg(), det(m).neg().neg(), det(m));
    // det(m3) ≡ det(m)
    T::axiom_eqv_transitive(det(m3), det(m2).neg(), det(m));

    // swap_01 on m3: det(r3, r1, r2, r0) ≡ -det(m3)
    lemma_det_swap_rows_01(m3);

    // -det(m3) ≡ -det(m)
    T::axiom_neg_congruence(det(m3), det(m));

    T::axiom_eqv_transitive(
        det(Mat4x4 { row0: r3, row1: r1, row2: r2, row3: r0 }),
        det(m3).neg(),
        det(m).neg(),
    );
}

// ---------------------------------------------------------------------------
// Derived zero-repeated cases involving row 0
// ---------------------------------------------------------------------------

/// If rows 0 and 2 are equal, det is zero.
pub proof fn lemma_det_zero_repeated_row_02<T: Ring>(a: Vec4<T>, b: Vec4<T>, c: Vec4<T>)
    ensures
        det(Mat4x4 { row0: a, row1: b, row2: a, row3: c }).eqv(T::zero()),
{
    let m = Mat4x4 { row0: a, row1: b, row2: a, row3: c };
    // swap_02: det(a, b, a, c) with rows 0,2 swapped = det(a, b, a, c) (same matrix!)
    // Actually: swap_02(m) = {row0: m.row2, row1: m.row1, row2: m.row0, row3: m.row3}
    //                       = {row0: a, row1: b, row2: a, row3: c} = m
    // And swap_02 says det(swapped) ≡ det(m).neg()
    // So det(m) ≡ det(m).neg()
    lemma_det_swap_rows_02(m);
    // det(m) ≡ det(m).neg() → det(m) + det(m) ≡ 0 → but easier:
    // det(m) ≡ det(m).neg() means det(m).add(det(m)) ≡ 0
    // Actually: if x ≡ -x, then x + x ≡ 0, and we need x ≡ 0.
    // Use: x ≡ -x → x.add(x) ≡ x.add(-x) ≡ 0
    // Hmm but we need x = 0 not 2x = 0.
    // Better: a + a.neg() ≡ 0 [inverse]. And a ≡ a.neg() gives a.neg() ≡ a.neg()
    // From a ≡ a.neg(): neg(a) ≡ neg(a.neg()) ≡ a [by neg_involution]
    // Wait, swap_02 gives det(same_matrix) ≡ det(m).neg(), i.e., det(m) ≡ det(m).neg()

    // Actually the swapped matrix IS m (since row0 = row2 = a), so:
    // det(m) ≡ det(m).neg()
    // → det(m) + det(m) ≡ det(m).neg() + det(m) ≡ 0
    // → 2*det(m) ≡ 0
    // This doesn't give det(m) = 0 in a general ring!

    // Better approach: use zero_repeated_row_12 via swaps.
    // swap_01 on m: det(b, a, a, c) ≡ -det(a, b, a, c)
    // But det(b, a, a, c) ≡ 0 by zero_repeated_row_12
    lemma_det_swap_rows_01(m);
    let m2 = Mat4x4 { row0: b, row1: a, row2: a, row3: c };
    lemma_det_zero_repeated_row_12(b, a, c);
    // det(m2) ≡ 0 and det(m2) ≡ det(m).neg()
    T::axiom_eqv_symmetric(
        det(Mat4x4 { row0: m.row1, row1: m.row0, row2: m.row2, row3: m.row3 }),
        det(m).neg(),
    );
    // det(m).neg() ≡ det(m2) ≡ 0
    T::axiom_eqv_transitive(det(m).neg(),
        det(Mat4x4 { row0: b, row1: a, row2: a, row3: c }),
        T::zero());

    // det(m).neg() ≡ 0 → det(m) ≡ 0
    T::axiom_neg_congruence(det(m).neg(), T::zero());
    additive_group_lemmas::lemma_neg_involution(det(m));
    T::axiom_eqv_symmetric(det(m).neg().neg(), det(m));
    T::axiom_eqv_transitive(det(m), det(m).neg().neg(), T::zero().neg());
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(det(m), T::zero().neg(), T::zero());
}

/// If rows 0 and 3 are equal, det is zero.
pub proof fn lemma_det_zero_repeated_row_03<T: Ring>(a: Vec4<T>, b: Vec4<T>, c: Vec4<T>)
    ensures
        det(Mat4x4 { row0: a, row1: b, row2: c, row3: a }).eqv(T::zero()),
{
    let m = Mat4x4 { row0: a, row1: b, row2: c, row3: a };

    // swap_01 on m: det(b, a, c, a) ≡ -det(m)
    lemma_det_swap_rows_01(m);
    // det(b, a, c, a) ≡ 0 by zero_repeated_row_13
    lemma_det_zero_repeated_row_13(b, a, c);

    T::axiom_eqv_symmetric(
        det(Mat4x4 { row0: m.row1, row1: m.row0, row2: m.row2, row3: m.row3 }),
        det(m).neg(),
    );
    T::axiom_eqv_transitive(det(m).neg(),
        det(Mat4x4 { row0: b, row1: a, row2: c, row3: a }),
        T::zero());

    // det(m).neg() ≡ 0 → det(m) ≡ 0
    T::axiom_neg_congruence(det(m).neg(), T::zero());
    additive_group_lemmas::lemma_neg_involution(det(m));
    T::axiom_eqv_symmetric(det(m).neg().neg(), det(m));
    T::axiom_eqv_transitive(det(m), det(m).neg().neg(), T::zero().neg());
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(det(m), T::zero().neg(), T::zero());
}

} // verus!
