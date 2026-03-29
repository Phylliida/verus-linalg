use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use crate::vec3::Vec3;
use crate::vec3::ops::{triple, cross, dot as dot3, scale as scale3};
use crate::vec4::Vec4;
use crate::mat3::Mat3x3;
use super::Mat4x4;
use super::ops::{det, transpose, drop_x, drop_y, drop_z, drop_w};

verus! {

//  ---------------------------------------------------------------------------
//  Helper: column-0 minor equivalences via Mat3x3 det_transpose
//  ---------------------------------------------------------------------------

///  Each cofactor triple of m^T is det3 of a transposed column-0 minor of m.
///  Applying Mat3x3 det_transpose gives: det3(N_i^T) ≡ det3(N_i).
///  This converts det(m^T) into the column-0 Laplace expansion of m.

///  Helper: triple of basis-vector cross products with one mul_commutative
///  Shows a.mul(b).sub(c.mul(d)) ≡ a.mul(b).sub(d.mul(c)) when c*d ≡ d*c.
proof fn lemma_sub_comm_right<T: Ring>(a: T, b: T, c: T, d: T)
    ensures a.mul(b).sub(c.mul(d)).eqv(a.mul(b).sub(d.mul(c)))
{
    T::axiom_eqv_reflexive(a.mul(b));
    T::axiom_mul_commutative(c, d);
    additive_group_lemmas::lemma_sub_congruence(a.mul(b), a.mul(b), c.mul(d), d.mul(c));
}

//  ---------------------------------------------------------------------------
//  Part A: det(m^T) ≡ column-0 expansion
//  ---------------------------------------------------------------------------

///  Shows: det(m^T) ≡ r0.x*det3(N0) - r1.x*det3(N1) + r2.x*det3(N2) - r3.x*det3(N3)
///  where N_i is the column-0 minor (delete row i and column 0).
proof fn lemma_det_mt_col0<T: Ring>(m: Mat4x4<T>)
    ensures
        det(transpose(m)).eqv(
            m.row0.x.mul(triple(drop_x(m.row1), drop_x(m.row2), drop_x(m.row3)))
            .sub(m.row1.x.mul(triple(drop_x(m.row0), drop_x(m.row2), drop_x(m.row3))))
            .add(m.row2.x.mul(triple(drop_x(m.row0), drop_x(m.row1), drop_x(m.row3))))
            .sub(m.row3.x.mul(triple(drop_x(m.row0), drop_x(m.row1), drop_x(m.row2))))
        ),
{
    let r0 = m.row0; let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;
    let mt = transpose(m);

    //  Construct Mat3x3 for each column-0 minor and apply det3_transpose.
    //  N0 = minor(row 0, col 0): rows are drop_x of r1, r2, r3
    let n0 = Mat3x3::<T> { row0: drop_x(r1), row1: drop_x(r2), row2: drop_x(r3) };
    crate::mat3::ops::lemma_det_transpose(n0);
    //  det3(transpose(n0)) ≡ det3(n0) = triple(dx(r1), dx(r2), dx(r3))
    //  And transpose(n0).row_k = dx(mt.row_{k+1}) structurally, so:
    //  triple(dx(mt.row1), dx(mt.row2), dx(mt.row3)) ≡ triple(dx(r1), dx(r2), dx(r3))

    let n1 = Mat3x3::<T> { row0: drop_x(r0), row1: drop_x(r2), row2: drop_x(r3) };
    crate::mat3::ops::lemma_det_transpose(n1);

    let n2 = Mat3x3::<T> { row0: drop_x(r0), row1: drop_x(r1), row2: drop_x(r3) };
    crate::mat3::ops::lemma_det_transpose(n2);

    let n3 = Mat3x3::<T> { row0: drop_x(r0), row1: drop_x(r1), row2: drop_x(r2) };
    crate::mat3::ops::lemma_det_transpose(n3);

    //  Now propagate the eqvs through the det formula.
    //  det(mt) = mt.row0.x * T_x - mt.row0.y * T_y + mt.row0.z * T_z - mt.row0.w * T_w
    //  mt.row0.x = r0.x, mt.row0.y = r1.x, mt.row0.z = r2.x, mt.row0.w = r3.x

    //  T_x = triple(dx(mt.row1), dx(mt.row2), dx(mt.row3)) ≡ triple(dx(r1), dx(r2), dx(r3))
    //  T_y = triple(dy(mt.row1), dy(mt.row2), dy(mt.row3)) ≡ triple(dx(r0), dx(r2), dx(r3))
    //  T_z = triple(dz(mt.row1), dz(mt.row2), dz(mt.row3)) ≡ triple(dx(r0), dx(r1), dx(r3))
    //  T_w = triple(dw(mt.row1), dw(mt.row2), dw(mt.row3)) ≡ triple(dx(r0), dx(r1), dx(r2))

    let t_x = triple(drop_x(mt.row1), drop_x(mt.row2), drop_x(mt.row3));
    let t_y = triple(drop_y(mt.row1), drop_y(mt.row2), drop_y(mt.row3));
    let t_z = triple(drop_z(mt.row1), drop_z(mt.row2), drop_z(mt.row3));
    let t_w = triple(drop_w(mt.row1), drop_w(mt.row2), drop_w(mt.row3));

    let a = triple(drop_x(r1), drop_x(r2), drop_x(r3));
    let b = triple(drop_x(r0), drop_x(r2), drop_x(r3));
    let c = triple(drop_x(r0), drop_x(r1), drop_x(r3));
    let d = triple(drop_x(r0), drop_x(r1), drop_x(r2));

    //  The structural equalities: dx(mt.row1) = transpose(n0).row0, etc.
    //  So t_x = det3(transpose(n0)) and det3_transpose gives t_x ≡ det3(n0) = a.
    //  Similarly for t_y, t_z, t_w.

    //  Propagate through multiplications
    T::axiom_eqv_reflexive(r0.x);
    ring_lemmas::lemma_mul_congruence::<T>(r0.x, r0.x, t_x, a);

    T::axiom_eqv_reflexive(r1.x);
    ring_lemmas::lemma_mul_congruence::<T>(r1.x, r1.x, t_y, b);

    T::axiom_eqv_reflexive(r2.x);
    ring_lemmas::lemma_mul_congruence::<T>(r2.x, r2.x, t_z, c);

    T::axiom_eqv_reflexive(r3.x);
    ring_lemmas::lemma_mul_congruence::<T>(r3.x, r3.x, t_w, d);

    //  Propagate through sub/add structure:
    //  det(mt) = ((r0.x*t_x - r1.x*t_y) + r2.x*t_z) - r3.x*t_w
    //  target  = ((r0.x*a - r1.x*b) + r2.x*c) - r3.x*d

    additive_group_lemmas::lemma_sub_congruence(
        r0.x.mul(t_x), r0.x.mul(a), r1.x.mul(t_y), r1.x.mul(b),
    );
    additive_group_lemmas::lemma_add_congruence(
        r0.x.mul(t_x).sub(r1.x.mul(t_y)),
        r0.x.mul(a).sub(r1.x.mul(b)),
        r2.x.mul(t_z),
        r2.x.mul(c),
    );
    additive_group_lemmas::lemma_sub_congruence(
        r0.x.mul(t_x).sub(r1.x.mul(t_y)).add(r2.x.mul(t_z)),
        r0.x.mul(a).sub(r1.x.mul(b)).add(r2.x.mul(c)),
        r3.x.mul(t_w),
        r3.x.mul(d),
    );
}

//  ---------------------------------------------------------------------------
//  Part B micro-helpers
//  ---------------------------------------------------------------------------

///  Normalize a.sub(b).add(c) into a.add(b.neg()).add(c).
proof fn lemma_sub_add_to_add_neg_add<T: Ring>(a: T, b: T, c: T)
    ensures a.sub(b).add(c).eqv(a.add(b.neg()).add(c))
{
    T::axiom_sub_is_add_neg(a, b);
    T::axiom_eqv_reflexive(c);
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.sub(b), a.add(b.neg()), c, c,
    );
}

///  dot distributes on the right: dot(a, b+c) ≡ dot(a,b) + dot(a,c).
proof fn lemma_dot3_distributes_right<T: Ring>(a: Vec3<T>, b: Vec3<T>, c: Vec3<T>)
    ensures dot3(a, b.add(c)).eqv(dot3(a, b).add(dot3(a, c)))
{
    let s1 = dot3(b.add(c), a);
    let s2 = dot3(b, a).add(dot3(c, a));

    //  dot(a, b+c) ≡ dot(b+c, a)
    crate::vec3::ops::lemma_dot_commutative::<T>(a, b.add(c));
    //  dot(b+c, a) ≡ dot(b,a) + dot(c,a)
    crate::vec3::ops::lemma_dot_distributes_left::<T>(b, c, a);
    //  dot(b,a) ≡ dot(a,b) and dot(c,a) ≡ dot(a,c)
    crate::vec3::ops::lemma_dot_commutative::<T>(b, a);
    crate::vec3::ops::lemma_dot_commutative::<T>(c, a);
    additive_group_lemmas::lemma_add_congruence::<T>(
        dot3(b, a), dot3(a, b),
        dot3(c, a), dot3(a, c),
    );
    //  Chain: dot(a, b+c) ≡ s1 ≡ s2 ≡ dot(a,b)+dot(a,c)
    T::axiom_eqv_transitive(dot3(a, b.add(c)), s1, s2);
    T::axiom_eqv_transitive(dot3(a, b.add(c)), s2, dot3(a, b).add(dot3(a, c)));
}

//  ---------------------------------------------------------------------------
//  Part B: column-0 expansion ≡ row-0 expansion
//  ---------------------------------------------------------------------------

//  ---------------------------------------------------------------------------
//  Part B coefficient helpers
//  ---------------------------------------------------------------------------
//  Each helper shows that a "collected coefficient" from the column-0
//  expansion matches (up to sign) the corresponding row-0 minor determinant.
//  The proof pattern: build the transposed 3×3 minor Q_j, apply det3_transpose,
//  then bridge the structural gap via mul_commutative on cross-product
//  subtrahends + sub_antisymmetric for the sign flip.

///  Commute subtrahend helper: a*b - c*d ≡ a*b - d*c
///  (used repeatedly to bridge cross product component differences)
proof fn lemma_sub_comm_subtrahend<T: Ring>(ab: T, c: T, d: T)
    ensures ab.sub(c.mul(d)).eqv(ab.sub(d.mul(c)))
{
    T::axiom_eqv_reflexive(ab);
    T::axiom_mul_commutative(c, d);
    additive_group_lemmas::lemma_sub_congruence(ab, ab, c.mul(d), d.mul(c));
}

///  x-coefficient: r1.x*P.x + r2.x*cx.y + r3.x*R.x ≡ r1.x*P.x - r2.x*Q.x + r3.x*R.x
///  where cx.y ≡ -Q.x via sub_antisymmetric + mul_commutative.
///
///  More precisely: det3(transpose(M01)) ≡ the x-collected-coefficient,
///  and det3_transpose gives det3(transpose(M01)) ≡ triple(dy(r1),dy(r2),dy(r3)).
proof fn lemma_coeff_x_match<T: Ring>(r1: Vec4<T>, r2: Vec4<T>, r3: Vec4<T>)
    ensures
        //  W.x ≡ B
        r1.x.mul(cross(drop_x(r2), drop_x(r3)).x)
            .sub(r2.x.mul(cross(drop_x(r1), drop_x(r3)).x))
            .add(r3.x.mul(cross(drop_x(r1), drop_x(r2)).x))
        .eqv(triple(drop_y(r1), drop_y(r2), drop_y(r3)))
{
    let p = cross(drop_x(r2), drop_x(r3));
    let q = cross(drop_x(r1), drop_x(r3));
    let rr = cross(drop_x(r1), drop_x(r2));

    //  Build N1 = Mat3{dy(r1), dy(r2), dy(r3)}, Q1 = transpose(N1)
    let n1 = Mat3x3::<T> { row0: drop_y(r1), row1: drop_y(r2), row2: drop_y(r3) };
    let q1t = crate::mat3::ops::transpose(n1);
    crate::mat3::ops::lemma_det_transpose(n1);
    //  det3(q1t) ≡ det3(n1) = triple(dy(r1), dy(r2), dy(r3))

    //  det3(q1t) = dot3(q1t.row0, cross(q1t.row1, q1t.row2))
    //            = r1.x*cx.x + r2.x*cx.y + r3.x*cx.z  (all adds)
    let cx = cross(q1t.row1, q1t.row2);

    //  cx.x ≡ p.x: subtrahends differ by mul_commutative
    lemma_sub_comm_subtrahend(q1t.row1.y.mul(q1t.row2.z), q1t.row1.z, q1t.row2.y);
    //  cx.x = q1t.row1.y*q1t.row2.z - q1t.row1.z*q1t.row2.y
    //       ≡ q1t.row1.y*q1t.row2.z - q1t.row2.y*q1t.row1.z = p.x

    //  cx.z ≡ rr.x: same pattern
    lemma_sub_comm_subtrahend(q1t.row1.x.mul(q1t.row2.y), q1t.row1.y, q1t.row2.x);

    //  cx.y ≡ q.x.neg(): sub_antisymmetric + mul_commutative
    //  cx.y = q1t.row1.z*q1t.row2.x - q1t.row1.x*q1t.row2.z
    //  q.x  = dx(r1).y*dx(r3).z - dx(r1).z*dx(r3).y
    //       = r1.z*r3.w - r1.w*r3.z
    //  cx.y has: r3.z*r1.w - r1.z*r3.w (structurally)
    //  Step 1: commute first term of cx.y
    T::axiom_mul_commutative(q1t.row1.z, q1t.row2.x); //  r3.z*r1.w ≡ r1.w*r3.z
    T::axiom_eqv_reflexive(q1t.row1.x.mul(q1t.row2.z));
    additive_group_lemmas::lemma_sub_congruence(
        q1t.row1.z.mul(q1t.row2.x), q1t.row2.x.mul(q1t.row1.z),
        q1t.row1.x.mul(q1t.row2.z), q1t.row1.x.mul(q1t.row2.z),
    );
    //  cx.y ≡ r1.w*r3.z - r1.z*r3.w
    //  Step 2: that's -(r1.z*r3.w - r1.w*r3.z) = -q.x by sub_antisymmetric
    additive_group_lemmas::lemma_sub_antisymmetric(
        q1t.row2.x.mul(q1t.row1.z), q1t.row1.x.mul(q1t.row2.z),
    );
    //  r1.w*r3.z - r1.z*r3.w ≡ -(r1.z*r3.w - r1.w*r3.z) = -q.x
    T::axiom_eqv_transitive(cx.y,
        q1t.row2.x.mul(q1t.row1.z).sub(q1t.row1.x.mul(q1t.row2.z)),
        q1t.row1.x.mul(q1t.row2.z).sub(q1t.row2.x.mul(q1t.row1.z)).neg());
    //  cx.y ≡ q.x.neg()

    //  Now propagate through multiplications:
    //  r1.x*cx.x ≡ r1.x*p.x
    T::axiom_eqv_reflexive(r1.x);
    ring_lemmas::lemma_mul_congruence(r1.x, r1.x, cx.x, p.x);
    //  r3.x*cx.z ≡ r3.x*rr.x
    T::axiom_eqv_reflexive(r3.x);
    ring_lemmas::lemma_mul_congruence(r3.x, r3.x, cx.z, rr.x);
    //  r2.x*cx.y ≡ r2.x*q.x.neg() ≡ (r2.x*q.x).neg()
    T::axiom_eqv_reflexive(r2.x);
    ring_lemmas::lemma_mul_congruence(r2.x, r2.x, cx.y, q.x.neg());
    ring_lemmas::lemma_mul_neg_right(r2.x, q.x);
    T::axiom_eqv_transitive(r2.x.mul(cx.y), r2.x.mul(q.x.neg()), r2.x.mul(q.x).neg());

    //  det3(q1t) = (r1.x*cx.x).add(r2.x*cx.y).add(r3.x*cx.z)  [dot, all adds]
    //  target    = (r1.x*p.x).sub(r2.x*q.x).add(r3.x*rr.x)     [sub-add pattern]

    //  Bridge first two terms: r1.x*cx.x + r2.x*cx.y ≡ r1.x*p.x + (r2.x*q.x).neg()
    additive_group_lemmas::lemma_add_congruence(
        r1.x.mul(cx.x), r1.x.mul(p.x),
        r2.x.mul(cx.y), r2.x.mul(q.x).neg(),
    );
    //  ... ≡ r1.x*p.x - r2.x*q.x  [by sub_is_add_neg reversed]
    T::axiom_sub_is_add_neg(r1.x.mul(p.x), r2.x.mul(q.x));
    T::axiom_eqv_symmetric(
        r1.x.mul(p.x).sub(r2.x.mul(q.x)),
        r1.x.mul(p.x).add(r2.x.mul(q.x).neg()),
    );
    T::axiom_eqv_transitive(
        r1.x.mul(cx.x).add(r2.x.mul(cx.y)),
        r1.x.mul(p.x).add(r2.x.mul(q.x).neg()),
        r1.x.mul(p.x).sub(r2.x.mul(q.x)),
    );

    //  Lift with third term: .add(r3.x*cx.z) ≡ .add(r3.x*rr.x)
    additive_group_lemmas::lemma_add_congruence(
        r1.x.mul(cx.x).add(r2.x.mul(cx.y)), r1.x.mul(p.x).sub(r2.x.mul(q.x)),
        r3.x.mul(cx.z), r3.x.mul(rr.x),
    );
    //  det3(q1t) ≡ W.x (the sub-add form)

    //  Chain with det3_transpose: W.x ≡ det3(q1t) ≡ det3(n1) = B
    T::axiom_eqv_symmetric(
        crate::mat3::ops::det(q1t),
        r1.x.mul(p.x).sub(r2.x.mul(q.x)).add(r3.x.mul(rr.x)),
    );
    T::axiom_eqv_transitive(
        r1.x.mul(p.x).sub(r2.x.mul(q.x)).add(r3.x.mul(rr.x)),
        crate::mat3::ops::det(q1t),
        triple(drop_y(r1), drop_y(r2), drop_y(r3)),
    );
}

///  y-coefficient: same pattern but with extra negation.
///  W.y ≡ -C = -triple(dz(r1), dz(r2), dz(r3))
proof fn lemma_coeff_y_match<T: Ring>(r1: Vec4<T>, r2: Vec4<T>, r3: Vec4<T>)
    ensures
        r1.x.mul(cross(drop_x(r2), drop_x(r3)).y)
            .sub(r2.x.mul(cross(drop_x(r1), drop_x(r3)).y))
            .add(r3.x.mul(cross(drop_x(r1), drop_x(r2)).y))
        .eqv(triple(drop_z(r1), drop_z(r2), drop_z(r3)).neg())
{
    let p = cross(drop_x(r2), drop_x(r3));
    let q = cross(drop_x(r1), drop_x(r3));
    let rr = cross(drop_x(r1), drop_x(r2));

    let n2 = Mat3x3::<T> { row0: drop_z(r1), row1: drop_z(r2), row2: drop_z(r3) };
    let q2t = crate::mat3::ops::transpose(n2);
    crate::mat3::ops::lemma_det_transpose(n2);
    //  det3(q2t) ≡ C = triple(dz(r1), dz(r2), dz(r3))

    let cx = cross(q2t.row1, q2t.row2);
    //  q2t: row0=(r1.x,r2.x,r3.x), row1=(r1.y,r2.y,r3.y), row2=(r1.w,r2.w,r3.w)

    //  --- cx.x ≡ -p.y: commute subtrahend then sub_antisymmetric ---
    lemma_sub_comm_subtrahend(q2t.row1.y.mul(q2t.row2.z), q2t.row1.z, q2t.row2.y);
    additive_group_lemmas::lemma_sub_antisymmetric(
        q2t.row1.y.mul(q2t.row2.z), q2t.row2.y.mul(q2t.row1.z),
    );
    T::axiom_eqv_transitive(cx.x,
        q2t.row1.y.mul(q2t.row2.z).sub(q2t.row2.y.mul(q2t.row1.z)),
        q2t.row2.y.mul(q2t.row1.z).sub(q2t.row1.y.mul(q2t.row2.z)).neg());

    //  --- cx.y ≡ q.y: just mul_comm on first term ---
    T::axiom_mul_commutative(q2t.row1.z, q2t.row2.x);
    T::axiom_eqv_reflexive(q2t.row1.x.mul(q2t.row2.z));
    additive_group_lemmas::lemma_sub_congruence(
        q2t.row1.z.mul(q2t.row2.x), q2t.row2.x.mul(q2t.row1.z),
        q2t.row1.x.mul(q2t.row2.z), q2t.row1.x.mul(q2t.row2.z),
    );

    //  --- cx.z ≡ -rr.y: commute subtrahend then sub_antisymmetric ---
    lemma_sub_comm_subtrahend(q2t.row1.x.mul(q2t.row2.y), q2t.row1.y, q2t.row2.x);
    additive_group_lemmas::lemma_sub_antisymmetric(
        q2t.row1.x.mul(q2t.row2.y), q2t.row2.x.mul(q2t.row1.y),
    );
    T::axiom_eqv_transitive(cx.z,
        q2t.row1.x.mul(q2t.row2.y).sub(q2t.row2.x.mul(q2t.row1.y)),
        q2t.row2.x.mul(q2t.row1.y).sub(q2t.row1.x.mul(q2t.row2.y)).neg());

    //  --- Propagate through multiplications ---
    T::axiom_eqv_reflexive(r1.x);
    ring_lemmas::lemma_mul_congruence(r1.x, r1.x, cx.x, p.y.neg());
    ring_lemmas::lemma_mul_neg_right(r1.x, p.y);
    T::axiom_eqv_transitive(r1.x.mul(cx.x), r1.x.mul(p.y.neg()), r1.x.mul(p.y).neg());

    T::axiom_eqv_reflexive(r2.x);
    ring_lemmas::lemma_mul_congruence(r2.x, r2.x, cx.y, q.y);

    T::axiom_eqv_reflexive(r3.x);
    ring_lemmas::lemma_mul_congruence(r3.x, r3.x, cx.z, rr.y.neg());
    ring_lemmas::lemma_mul_neg_right(r3.x, rr.y);
    T::axiom_eqv_transitive(r3.x.mul(cx.z), r3.x.mul(rr.y.neg()), r3.x.mul(rr.y).neg());

    //  --- det3(q2t) ≡ E = (-a' + b') + (-c') ---
    let a_prime = r1.x.mul(p.y);
    let b_prime = r2.x.mul(q.y);
    let c_prime = r3.x.mul(rr.y);
    additive_group_lemmas::lemma_add_congruence(
        r1.x.mul(cx.x), a_prime.neg(),
        r2.x.mul(cx.y), b_prime,
    );
    additive_group_lemmas::lemma_add_congruence(
        r1.x.mul(cx.x).add(r2.x.mul(cx.y)),
        a_prime.neg().add(b_prime),
        r3.x.mul(cx.z), c_prime.neg(),
    );
    //  Z3 sees det3(q2t) == all-adds-form ≡ E

    //  --- Negate: E.neg() ≡ W.y = a'.sub(b').add(c') ---
    //  E = (a'.neg() + b') + c'.neg()  (left-assoc)
    //  -E ≡ -(a'.neg() + b') + -(c'.neg())  [neg_add]
    additive_group_lemmas::lemma_neg_add(a_prime.neg().add(b_prime), c_prime.neg());
    //  -(a'.neg() + b') ≡ a'.neg().neg() + b'.neg()  [neg_add]
    additive_group_lemmas::lemma_neg_add(a_prime.neg(), b_prime);
    //  a'.neg().neg() ≡ a'  [neg_involution]
    additive_group_lemmas::lemma_neg_involution(a_prime);
    //  c'.neg().neg() ≡ c'  [neg_involution]
    additive_group_lemmas::lemma_neg_involution(c_prime);

    //  Assemble: -(a'.neg() + b') ≡ a' + b'.neg()
    T::axiom_eqv_reflexive(b_prime.neg());
    additive_group_lemmas::lemma_add_congruence(
        a_prime.neg().neg(), a_prime,
        b_prime.neg(), b_prime.neg(),
    );
    T::axiom_eqv_transitive(
        a_prime.neg().add(b_prime).neg(),
        a_prime.neg().neg().add(b_prime.neg()),
        a_prime.add(b_prime.neg()),
    );

    //  a' + b'.neg() ≡ a' - b'  [sub_is_add_neg reversed]
    T::axiom_sub_is_add_neg(a_prime, b_prime);
    T::axiom_eqv_symmetric(a_prime.sub(b_prime), a_prime.add(b_prime.neg()));
    T::axiom_eqv_transitive(
        a_prime.neg().add(b_prime).neg(),
        a_prime.add(b_prime.neg()),
        a_prime.sub(b_prime),
    );

    //  E.neg() ≡ (a' - b') + c'
    additive_group_lemmas::lemma_add_congruence(
        a_prime.neg().add(b_prime).neg(), a_prime.sub(b_prime),
        c_prime.neg().neg(), c_prime,
    );
    T::axiom_eqv_transitive(
        a_prime.neg().add(b_prime).add(c_prime.neg()).neg(),
        a_prime.neg().add(b_prime).neg().add(c_prime.neg().neg()),
        a_prime.sub(b_prime).add(c_prime),
    );
    //  E.neg() ≡ W.y

    //  --- Final chain: W.y ≡ -C ---
    //  E ≡ det3(q2t) ≡ C, so E.neg() ≡ C.neg()
    T::axiom_eqv_symmetric(
        crate::mat3::ops::det(q2t),
        a_prime.neg().add(b_prime).add(c_prime.neg()),
    );
    T::axiom_eqv_transitive(
        a_prime.neg().add(b_prime).add(c_prime.neg()),
        crate::mat3::ops::det(q2t),
        triple(drop_z(r1), drop_z(r2), drop_z(r3)),
    );
    additive_group_lemmas::lemma_neg_congruence(
        a_prime.neg().add(b_prime).add(c_prime.neg()),
        triple(drop_z(r1), drop_z(r2), drop_z(r3)),
    );
    //  E.neg() ≡ C.neg()

    //  W.y ≡ E.neg() ≡ C.neg()
    T::axiom_eqv_symmetric(
        a_prime.neg().add(b_prime).add(c_prime.neg()).neg(),
        a_prime.sub(b_prime).add(c_prime),
    );
    T::axiom_eqv_transitive(
        a_prime.sub(b_prime).add(c_prime),
        a_prime.neg().add(b_prime).add(c_prime.neg()).neg(),
        triple(drop_z(r1), drop_z(r2), drop_z(r3)).neg(),
    );
}

///  z-coefficient: W.z ≡ D = triple(dw(r1), dw(r2), dw(r3))
///  Same pattern as coeff_x (positive sign, no extra negation).
proof fn lemma_coeff_z_match<T: Ring>(r1: Vec4<T>, r2: Vec4<T>, r3: Vec4<T>)
    ensures
        r1.x.mul(cross(drop_x(r2), drop_x(r3)).z)
            .sub(r2.x.mul(cross(drop_x(r1), drop_x(r3)).z))
            .add(r3.x.mul(cross(drop_x(r1), drop_x(r2)).z))
        .eqv(triple(drop_w(r1), drop_w(r2), drop_w(r3)))
{
    let p = cross(drop_x(r2), drop_x(r3));
    let q = cross(drop_x(r1), drop_x(r3));
    let rr = cross(drop_x(r1), drop_x(r2));

    let n3 = Mat3x3::<T> { row0: drop_w(r1), row1: drop_w(r2), row2: drop_w(r3) };
    let q3t = crate::mat3::ops::transpose(n3);
    crate::mat3::ops::lemma_det_transpose(n3);

    let cx = cross(q3t.row1, q3t.row2);

    //  q3t.row0 = (r1.x, r2.x, r3.x)
    //  q3t.row1 = (r1.y, r2.y, r3.y)   [drop_w(ri).y = ri.y]
    //  q3t.row2 = (r1.z, r2.z, r3.z)   [drop_w(ri).z = ri.z]

    //  cx.x = r2.y*r3.z - r3.y*r2.z ≡ r2.y*r3.z - r2.z*r3.y = p.z [mul_comm subtrahend]
    lemma_sub_comm_subtrahend(q3t.row1.y.mul(q3t.row2.z), q3t.row1.z, q3t.row2.y);

    //  cx.z = r1.y*r2.z - r2.y*r1.z ≡ r1.y*r2.z - r1.z*r2.y = rr.z [mul_comm subtrahend]
    lemma_sub_comm_subtrahend(q3t.row1.x.mul(q3t.row2.y), q3t.row1.y, q3t.row2.x);

    //  cx.y: r3.y*r1.z - r1.y*r3.z
    //  q.z = r1.y*r3.z - r1.z*r3.y ... wait let me check
    //  q.z = cross(dx(r1), dx(r3)).z = dx(r1).x*dx(r3).y - dx(r1).y*dx(r3).x
    //      = r1.y*r3.z - r1.z*r3.y
    //  cx.y = q3t.row1.z*q3t.row2.x - q3t.row1.x*q3t.row2.z
    //       = r3.y*r1.z - r1.y*r3.z
    //  cx.y ≡ r1.z*r3.y - r1.y*r3.z [mul_comm on first term]
    //       = -(r1.y*r3.z - r1.z*r3.y) = -q.z [sub_antisymmetric]
    T::axiom_mul_commutative(q3t.row1.z, q3t.row2.x);
    T::axiom_eqv_reflexive(q3t.row1.x.mul(q3t.row2.z));
    additive_group_lemmas::lemma_sub_congruence(
        q3t.row1.z.mul(q3t.row2.x), q3t.row2.x.mul(q3t.row1.z),
        q3t.row1.x.mul(q3t.row2.z), q3t.row1.x.mul(q3t.row2.z),
    );
    additive_group_lemmas::lemma_sub_antisymmetric(
        q3t.row2.x.mul(q3t.row1.z), q3t.row1.x.mul(q3t.row2.z),
    );
    T::axiom_eqv_transitive(cx.y,
        q3t.row2.x.mul(q3t.row1.z).sub(q3t.row1.x.mul(q3t.row2.z)),
        q3t.row1.x.mul(q3t.row2.z).sub(q3t.row2.x.mul(q3t.row1.z)).neg());

    //  Propagate through multiplications
    T::axiom_eqv_reflexive(r1.x);
    ring_lemmas::lemma_mul_congruence(r1.x, r1.x, cx.x, p.z);
    T::axiom_eqv_reflexive(r3.x);
    ring_lemmas::lemma_mul_congruence(r3.x, r3.x, cx.z, rr.z);
    T::axiom_eqv_reflexive(r2.x);
    ring_lemmas::lemma_mul_congruence(r2.x, r2.x, cx.y, q.z.neg());
    ring_lemmas::lemma_mul_neg_right(r2.x, q.z);
    T::axiom_eqv_transitive(r2.x.mul(cx.y), r2.x.mul(q.z.neg()), r2.x.mul(q.z).neg());

    //  Bridge: all-adds → sub-add
    additive_group_lemmas::lemma_add_congruence(
        r1.x.mul(cx.x), r1.x.mul(p.z),
        r2.x.mul(cx.y), r2.x.mul(q.z).neg(),
    );
    T::axiom_sub_is_add_neg(r1.x.mul(p.z), r2.x.mul(q.z));
    T::axiom_eqv_symmetric(
        r1.x.mul(p.z).sub(r2.x.mul(q.z)),
        r1.x.mul(p.z).add(r2.x.mul(q.z).neg()),
    );
    T::axiom_eqv_transitive(
        r1.x.mul(cx.x).add(r2.x.mul(cx.y)),
        r1.x.mul(p.z).add(r2.x.mul(q.z).neg()),
        r1.x.mul(p.z).sub(r2.x.mul(q.z)),
    );
    additive_group_lemmas::lemma_add_congruence(
        r1.x.mul(cx.x).add(r2.x.mul(cx.y)), r1.x.mul(p.z).sub(r2.x.mul(q.z)),
        r3.x.mul(cx.z), r3.x.mul(rr.z),
    );

    //  Chain: W.z ≡ det3(q3t) ≡ det3(n3) = D
    T::axiom_eqv_symmetric(
        crate::mat3::ops::det(q3t),
        r1.x.mul(p.z).sub(r2.x.mul(q.z)).add(r3.x.mul(rr.z)),
    );
    T::axiom_eqv_transitive(
        r1.x.mul(p.z).sub(r2.x.mul(q.z)).add(r3.x.mul(rr.z)),
        crate::mat3::ops::det(q3t),
        triple(drop_w(r1), drop_w(r2), drop_w(r3)),
    );
}

//  ---------------------------------------------------------------------------
//  Part B structural helpers
//  ---------------------------------------------------------------------------

///  ((x - a) + b) - c ≡ x - ((a - b) + c)
///  Converts left-associated sub-add-sub into x minus a single remainder.
proof fn lemma_sub_add_sub_assoc<T: Ring>(x: T, a: T, b: T, c: T)
    ensures x.sub(a).add(b).sub(c).eqv(x.sub(a.sub(b).add(c)))
{
    //  LHS all-adds: x + (-a + (b + (-c)))
    //  RHS all-adds: x + (-(a-b+c))
    //  Both equal x + (-a + b + (-c)) after neg distribution.

    //  Convert LHS: ((x-a)+b)-c → x + ((-a+b)+(-c))
    T::axiom_sub_is_add_neg(x, a);
    T::axiom_eqv_reflexive(b);
    additive_group_lemmas::lemma_add_congruence(x.sub(a), x.add(a.neg()), b, b);
    T::axiom_sub_is_add_neg(x.sub(a).add(b), c);
    //  x.sub(a).add(b).sub(c) ≡ x.sub(a).add(b).add(c.neg())
    //                          ≡ x.add(a.neg()).add(b).add(c.neg())
    T::axiom_eqv_reflexive(c.neg());
    additive_group_lemmas::lemma_add_congruence(
        x.sub(a).add(b), x.add(a.neg()).add(b), c.neg(), c.neg(),
    );
    T::axiom_eqv_transitive(
        x.sub(a).add(b).sub(c),
        x.sub(a).add(b).add(c.neg()),
        x.add(a.neg()).add(b).add(c.neg()),
    );
    //  LHS ≡ ((x + (-a)) + b) + (-c)

    //  Re-associate: ((x+(-a))+b)+(-c) → x + ((-a+b)+(-c))
    T::axiom_add_associative(x, a.neg(), b);
    T::axiom_eqv_reflexive(c.neg());
    additive_group_lemmas::lemma_add_congruence(
        x.add(a.neg()).add(b), x.add(a.neg().add(b)), c.neg(), c.neg(),
    );
    T::axiom_add_associative(x, a.neg().add(b), c.neg());
    T::axiom_eqv_transitive(
        x.add(a.neg()).add(b).add(c.neg()),
        x.add(a.neg().add(b)).add(c.neg()),
        x.add(a.neg().add(b).add(c.neg())),
    );
    //  LHS ≡ x + ((-a + b) + (-c))

    //  Convert RHS: x - ((a-b)+c)
    //  -(a-b+c) = -(a+(-b)+c) → (-a+b)+(-c)
    T::axiom_sub_is_add_neg(a, b);
    T::axiom_eqv_reflexive(c);
    additive_group_lemmas::lemma_add_congruence(a.sub(b), a.add(b.neg()), c, c);
    //  (a-b)+c ≡ (a+(-b))+c
    additive_group_lemmas::lemma_neg_congruence(a.sub(b).add(c), a.add(b.neg()).add(c));
    //  -(a-b+c) ≡ -((a+(-b))+c)

    additive_group_lemmas::lemma_neg_add(a.add(b.neg()), c);
    //  -((a+(-b))+c) ≡ -(a+(-b)) + (-c)
    additive_group_lemmas::lemma_neg_add(a, b.neg());
    //  -(a+(-b)) ≡ (-a) + (-(-b))
    additive_group_lemmas::lemma_neg_involution(b);
    //  (-(-b)) ≡ b
    T::axiom_eqv_reflexive(a.neg());
    additive_group_lemmas::lemma_add_congruence(a.neg(), a.neg(), b.neg().neg(), b);
    T::axiom_eqv_transitive(
        a.add(b.neg()).neg(),
        a.neg().add(b.neg().neg()),
        a.neg().add(b),
    );
    //  -(a+(-b)) ≡ (-a) + b

    T::axiom_eqv_reflexive(c.neg());
    additive_group_lemmas::lemma_add_congruence(
        a.add(b.neg()).neg(), a.neg().add(b), c.neg(), c.neg(),
    );
    T::axiom_eqv_transitive(
        a.add(b.neg()).add(c).neg(),
        a.add(b.neg()).neg().add(c.neg()),
        a.neg().add(b).add(c.neg()),
    );
    //  -((a+(-b))+c) ≡ (-a+b)+(-c)

    T::axiom_eqv_transitive(
        a.sub(b).add(c).neg(),
        a.add(b.neg()).add(c).neg(),
        a.neg().add(b).add(c.neg()),
    );
    //  -(a-b+c) ≡ (-a+b)+(-c)

    //  RHS = x + (-(a-b+c)) ≡ x + ((-a+b)+(-c))
    T::axiom_sub_is_add_neg(x, a.sub(b).add(c));
    T::axiom_eqv_reflexive(x);
    additive_group_lemmas::lemma_add_congruence(
        x, x, a.sub(b).add(c).neg(), a.neg().add(b).add(c.neg()),
    );
    T::axiom_eqv_transitive(
        x.sub(a.sub(b).add(c)),
        x.add(a.sub(b).add(c).neg()),
        x.add(a.neg().add(b).add(c.neg())),
    );
    //  RHS ≡ x + ((-a+b)+(-c))

    //  Chain: LHS ≡ x+((-a+b)+(-c)) ≡ RHS
    T::axiom_eqv_transitive(
        x.sub(a).add(b).sub(c),
        x.add(a.neg()).add(b).add(c.neg()),
        x.add(a.neg().add(b).add(c.neg())),
    );
    T::axiom_eqv_symmetric(
        x.sub(a.sub(b).add(c)),
        x.add(a.neg().add(b).add(c.neg())),
    );
    T::axiom_eqv_transitive(
        x.sub(a).add(b).sub(c),
        x.add(a.neg().add(b).add(c.neg())),
        x.sub(a.sub(b).add(c)),
    );
}

///  dot3(a, u - v) ≡ dot3(a, u) - dot3(a, v)
proof fn lemma_dot3_sub_right<T: Ring>(a: Vec3<T>, u: Vec3<T>, v: Vec3<T>)
    ensures dot3(a, u.sub(v)).eqv(dot3(a, u).sub(dot3(a, v)))
{
    //  u - v ≡ u + (-v) [Vec3 sub_is_add_neg]
    Vec3::<T>::axiom_sub_is_add_neg(u, v);
    Vec3::<T>::axiom_eqv_reflexive(a);
    crate::vec3::ops::lemma_dot_congruence(a, a, u.sub(v), u.add(v.neg()));
    //  dot3(a, u-v) ≡ dot3(a, u+(-v))

    //  dot3(a, u+(-v)) ≡ dot3(a,u) + dot3(a, -v)
    lemma_dot3_distributes_right(a, u, v.neg());

    //  dot3(a, -v) ≡ -dot3(a, v)
    crate::vec3::ops::lemma_dot_neg_right(a, v);

    //  dot3(a,u) + dot3(a,-v) ≡ dot3(a,u) + (-dot3(a,v))
    T::axiom_eqv_reflexive(dot3(a, u));
    additive_group_lemmas::lemma_add_congruence(
        dot3(a, u), dot3(a, u), dot3(a, v.neg()), dot3(a, v).neg(),
    );

    //  dot3(a,u) + (-dot3(a,v)) ≡ dot3(a,u) - dot3(a,v)
    T::axiom_sub_is_add_neg(dot3(a, u), dot3(a, v));
    T::axiom_eqv_symmetric(
        dot3(a, u).sub(dot3(a, v)),
        dot3(a, u).add(dot3(a, v).neg()),
    );

    //  Chain: dot3(a, u-v) ≡ dot3(a, u+(-v)) ≡ dot3(a,u)+dot3(a,-v) ≡ dot3(a,u)+(-dot3(a,v)) ≡ dot3(a,u)-dot3(a,v)
    T::axiom_eqv_transitive(
        dot3(a, u.sub(v)), dot3(a, u.add(v.neg())),
        dot3(a, u).add(dot3(a, v.neg())),
    );
    T::axiom_eqv_transitive(
        dot3(a, u.sub(v)),
        dot3(a, u).add(dot3(a, v.neg())),
        dot3(a, u).add(dot3(a, v).neg()),
    );
    T::axiom_eqv_transitive(
        dot3(a, u.sub(v)),
        dot3(a, u).add(dot3(a, v).neg()),
        dot3(a, u).sub(dot3(a, v)),
    );
}

//  ---------------------------------------------------------------------------
//  Part B: column-0 expansion ≡ det(m)
//  ---------------------------------------------------------------------------

///  Part B: column-0 Laplace expansion ≡ det(m) (row-0 Laplace expansion).
///  Both reduce to F.sub(remainder) via lemma_sub_add_sub_assoc, then the
///  remainders are matched via dot3 factoring + coefficient helpers.
proof fn lemma_col0_eq_det<T: Ring>(m: Mat4x4<T>)
    ensures
        m.row0.x.mul(triple(drop_x(m.row1), drop_x(m.row2), drop_x(m.row3)))
            .sub(m.row1.x.mul(triple(drop_x(m.row0), drop_x(m.row2), drop_x(m.row3))))
            .add(m.row2.x.mul(triple(drop_x(m.row0), drop_x(m.row1), drop_x(m.row3))))
            .sub(m.row3.x.mul(triple(drop_x(m.row0), drop_x(m.row1), drop_x(m.row2))))
        .eqv(det(m)),
{
    let r0 = m.row0; let r1 = m.row1; let r2 = m.row2; let r3 = m.row3;
    let a = drop_x(r0);
    let p = cross(drop_x(r2), drop_x(r3));
    let q = cross(drop_x(r1), drop_x(r3));
    let rr = cross(drop_x(r1), drop_x(r2));

    let F = r0.x.mul(triple(drop_x(r1), drop_x(r2), drop_x(r3)));
    let A = r1.x.mul(triple(drop_x(r0), drop_x(r2), drop_x(r3)));
    let Bt = r2.x.mul(triple(drop_x(r0), drop_x(r1), drop_x(r3)));
    let Ct = r3.x.mul(triple(drop_x(r0), drop_x(r1), drop_x(r2)));

    let B = triple(drop_y(r1), drop_y(r2), drop_y(r3));
    let C = triple(drop_z(r1), drop_z(r2), drop_z(r3));
    let D = triple(drop_w(r1), drop_w(r2), drop_w(r3));

    let sp = scale3(r1.x, p);
    let sq = scale3(r2.x, q);
    let srr = scale3(r3.x, rr);

    //  ---- col0 ≡ F.sub(col_rem) ----
    lemma_sub_add_sub_assoc(F, A, Bt, Ct);
    //  col0 = ((F-A)+Bt)-Ct ≡ F.sub(A.sub(Bt).add(Ct))
    let col_rem = A.sub(Bt).add(Ct);

    //  ---- col_rem ≡ dot3(a, W') ----
    //  A = r1.x*T1 ≡ dot3(a, sp) via dot_scale_right
    crate::vec3::ops::lemma_dot_scale_right(r1.x, a, p);
    T::axiom_eqv_symmetric(dot3(a, sp), r1.x.mul(dot3(a, p)));
    //  Bt ≡ dot3(a, sq)
    crate::vec3::ops::lemma_dot_scale_right(r2.x, a, q);
    T::axiom_eqv_symmetric(dot3(a, sq), r2.x.mul(dot3(a, q)));
    //  Ct ≡ dot3(a, srr)
    crate::vec3::ops::lemma_dot_scale_right(r3.x, a, rr);
    T::axiom_eqv_symmetric(dot3(a, srr), r3.x.mul(dot3(a, rr)));

    //  col_rem = A.sub(Bt).add(Ct) ≡ dot3(a,sp).sub(dot3(a,sq)).add(dot3(a,srr))
    additive_group_lemmas::lemma_sub_congruence(A, dot3(a, sp), Bt, dot3(a, sq));
    T::axiom_eqv_reflexive(Ct);
    additive_group_lemmas::lemma_add_congruence(
        A.sub(Bt), dot3(a, sp).sub(dot3(a, sq)), Ct, Ct,
    );
    T::axiom_eqv_reflexive(dot3(a, srr));
    additive_group_lemmas::lemma_add_congruence(
        A.sub(Bt), dot3(a, sp).sub(dot3(a, sq)), Ct, dot3(a, srr),
    );
    //  Hmm, I applied add_congruence twice with different second args. Let me redo:
    //  Need: A.sub(Bt).add(Ct) ≡ dot3(a,sp).sub(dot3(a,sq)).add(dot3(a,srr))
    additive_group_lemmas::lemma_add_congruence(
        A.sub(Bt), dot3(a, sp).sub(dot3(a, sq)),
        Ct, dot3(a, srr),
    );
    //  col_rem ≡ dot3(a,sp).sub(dot3(a,sq)).add(dot3(a,srr))

    //  dot3(a,sp).sub(dot3(a,sq)) ≡ dot3(a, sp.sub(sq))
    lemma_dot3_sub_right(a, sp, sq);
    T::axiom_eqv_symmetric(dot3(a, sp.sub(sq)), dot3(a, sp).sub(dot3(a, sq)));
    //  dot3(a,sp) - dot3(a,sq) ≡ dot3(a, sp-sq)

    //  Lift: dot3(a, sp-sq) + dot3(a, srr) ≡ dot3(a, (sp-sq)+srr) = dot3(a, W')
    lemma_dot3_distributes_right(a, sp.sub(sq), srr);
    T::axiom_eqv_symmetric(
        dot3(a, sp.sub(sq).add(srr)),
        dot3(a, sp.sub(sq)).add(dot3(a, srr)),
    );

    //  Chain: col_rem ≡ dot3(a,sp)-dot3(a,sq)+dot3(a,srr) ≡ dot3(a,sp-sq)+dot3(a,srr) ≡ dot3(a,W')
    T::axiom_eqv_reflexive(dot3(a, srr));
    additive_group_lemmas::lemma_add_congruence(
        dot3(a, sp).sub(dot3(a, sq)), dot3(a, sp.sub(sq)),
        dot3(a, srr), dot3(a, srr),
    );
    T::axiom_eqv_transitive(
        dot3(a, sp).sub(dot3(a, sq)).add(dot3(a, srr)),
        dot3(a, sp.sub(sq)).add(dot3(a, srr)),
        dot3(a, sp.sub(sq).add(srr)),
    );
    T::axiom_eqv_transitive(
        col_rem,
        dot3(a, sp).sub(dot3(a, sq)).add(dot3(a, srr)),
        dot3(a, sp.sub(sq).add(srr)),
    );
    let W_prime = sp.sub(sq).add(srr);
    //  col_rem ≡ dot3(a, W')

    //  ---- dot3(a, W') ≡ det_sub_rem ----
    //  W'.x = Wx, W'.y = Wy, W'.z = Wz structurally (Z3 sees via open spec unfolding)
    //  Coeff helpers: Wx ≡ B, Wy ≡ -C, Wz ≡ D
    lemma_coeff_x_match(r1, r2, r3);
    lemma_coeff_y_match(r1, r2, r3);
    lemma_coeff_z_match(r1, r2, r3);

    //  dot3(a, W') = r0.y*W'.x + r0.z*W'.y + r0.w*W'.z
    //  ≡ r0.y*B + r0.z*(-C) + r0.w*D  [mul_congruence]
    T::axiom_eqv_reflexive(r0.y);
    ring_lemmas::lemma_mul_congruence(r0.y, r0.y, W_prime.x, B);
    T::axiom_eqv_reflexive(r0.z);
    ring_lemmas::lemma_mul_congruence(r0.z, r0.z, W_prime.y, C.neg());
    T::axiom_eqv_reflexive(r0.w);
    ring_lemmas::lemma_mul_congruence(r0.w, r0.w, W_prime.z, D);

    additive_group_lemmas::lemma_add_congruence(
        r0.y.mul(W_prime.x), r0.y.mul(B),
        r0.z.mul(W_prime.y), r0.z.mul(C.neg()),
    );
    additive_group_lemmas::lemma_add_congruence(
        r0.y.mul(W_prime.x).add(r0.z.mul(W_prime.y)),
        r0.y.mul(B).add(r0.z.mul(C.neg())),
        r0.w.mul(W_prime.z), r0.w.mul(D),
    );
    //  dot3(a, W') ≡ (r0.y*B + r0.z*(-C)) + r0.w*D

    //  Bridge r0.z*(-C) to -(r0.z*C) using mul_neg_right
    ring_lemmas::lemma_mul_neg_right(r0.z, C);
    //  r0.z*C.neg() ≡ (r0.z*C).neg()

    //  (r0.y*B + r0.z*(-C)) ≡ (r0.y*B + -(r0.z*C)) ≡ r0.y*B - r0.z*C
    T::axiom_eqv_reflexive(r0.y.mul(B));
    additive_group_lemmas::lemma_add_congruence(
        r0.y.mul(B), r0.y.mul(B),
        r0.z.mul(C.neg()), r0.z.mul(C).neg(),
    );
    T::axiom_sub_is_add_neg(r0.y.mul(B), r0.z.mul(C));
    T::axiom_eqv_symmetric(r0.y.mul(B).sub(r0.z.mul(C)), r0.y.mul(B).add(r0.z.mul(C).neg()));
    T::axiom_eqv_transitive(
        r0.y.mul(B).add(r0.z.mul(C.neg())),
        r0.y.mul(B).add(r0.z.mul(C).neg()),
        r0.y.mul(B).sub(r0.z.mul(C)),
    );

    //  Lift with r0.w*D
    T::axiom_eqv_reflexive(r0.w.mul(D));
    additive_group_lemmas::lemma_add_congruence(
        r0.y.mul(B).add(r0.z.mul(C.neg())),
        r0.y.mul(B).sub(r0.z.mul(C)),
        r0.w.mul(D), r0.w.mul(D),
    );
    T::axiom_eqv_transitive(
        dot3(a, W_prime),
        r0.y.mul(B).add(r0.z.mul(C.neg())).add(r0.w.mul(D)),
        r0.y.mul(B).sub(r0.z.mul(C)).add(r0.w.mul(D)),
    );
    let det_sub_rem = r0.y.mul(B).sub(r0.z.mul(C)).add(r0.w.mul(D));
    //  dot3(a, W') ≡ det_sub_rem

    //  ---- col_rem ≡ det_sub_rem ----
    T::axiom_eqv_transitive(col_rem, dot3(a, W_prime), det_sub_rem);

    //  ---- F.sub(col_rem) ≡ F.sub(det_sub_rem) ----
    T::axiom_eqv_reflexive(F);
    additive_group_lemmas::lemma_sub_congruence(F, F, col_rem, det_sub_rem);

    //  ---- det(m) ≡ F.sub(det_sub_rem) ----
    lemma_sub_add_sub_assoc(F, r0.y.mul(B), r0.z.mul(C), r0.w.mul(D));
    //  det(m) = ((F - r0.y*B) + r0.z*C) - r0.w*D ≡ F.sub(det_sub_rem)

    //  ---- col0 ≡ det(m) ----
    //  col0 ≡ F.sub(col_rem) [from sub_add_sub_assoc]
    //  F.sub(col_rem) ≡ F.sub(det_sub_rem) [from above]
    //  det(m) ≡ F.sub(det_sub_rem) [from sub_add_sub_assoc]
    T::axiom_eqv_transitive(
        F.sub(A).add(Bt).sub(Ct),
        F.sub(col_rem),
        F.sub(det_sub_rem),
    );
    T::axiom_eqv_symmetric(
        F.sub(r0.y.mul(B)).add(r0.z.mul(C)).sub(r0.w.mul(D)),
        F.sub(det_sub_rem),
    );
    T::axiom_eqv_transitive(
        F.sub(A).add(Bt).sub(Ct),
        F.sub(det_sub_rem),
        F.sub(r0.y.mul(B)).add(r0.z.mul(C)).sub(r0.w.mul(D)),
    );
}

//  ---------------------------------------------------------------------------
//  Main theorem
//  ---------------------------------------------------------------------------

pub proof fn lemma_det_transpose<T: Ring>(m: Mat4x4<T>)
    ensures det(transpose(m)).eqv(det(m))
{
    let col0 = m.row0.x.mul(triple(drop_x(m.row1), drop_x(m.row2), drop_x(m.row3)))
        .sub(m.row1.x.mul(triple(drop_x(m.row0), drop_x(m.row2), drop_x(m.row3))))
        .add(m.row2.x.mul(triple(drop_x(m.row0), drop_x(m.row1), drop_x(m.row3))))
        .sub(m.row3.x.mul(triple(drop_x(m.row0), drop_x(m.row1), drop_x(m.row2))));

    //  Part A: det(m^T) ≡ col0 (column-0 Laplace expansion)
    lemma_det_mt_col0(m);

    //  Part B: col0 ≡ det(m) (column-0 = row-0 Laplace expansion)
    lemma_col0_eq_det(m);

    //  Chain: det(m^T) ≡ col0 ≡ det(m)
    T::axiom_eqv_transitive(det(transpose(m)), col0, det(m));
}

} //  verus!
