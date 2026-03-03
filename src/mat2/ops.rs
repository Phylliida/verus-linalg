use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_commutative_monoid_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::field_lemmas;
use crate::vec2::Vec2;
use crate::vec2::ops::{dot, scale};
use super::Mat2x2;

verus! {

// ---------------------------------------------------------------------------
// Spec functions
// ---------------------------------------------------------------------------

pub open spec fn identity<T: Ring>() -> Mat2x2<T> {
    Mat2x2 {
        row0: Vec2 { x: T::one(), y: T::zero() },
        row1: Vec2 { x: T::zero(), y: T::one() },
    }
}

pub open spec fn mat_vec_mul<T: Ring>(m: Mat2x2<T>, v: Vec2<T>) -> Vec2<T> {
    Vec2 { x: dot(m.row0, v), y: dot(m.row1, v) }
}

pub open spec fn transpose<T: Ring>(m: Mat2x2<T>) -> Mat2x2<T> {
    Mat2x2 {
        row0: Vec2 { x: m.row0.x, y: m.row1.x },
        row1: Vec2 { x: m.row0.y, y: m.row1.y },
    }
}

pub open spec fn det<T: Ring>(m: Mat2x2<T>) -> T {
    m.row0.x.mul(m.row1.y).sub(m.row0.y.mul(m.row1.x))
}

pub open spec fn mat_mul<T: Ring>(a: Mat2x2<T>, b: Mat2x2<T>) -> Mat2x2<T> {
    let bt = transpose(b);
    Mat2x2 {
        row0: Vec2 {
            x: dot(a.row0, bt.row0),
            y: dot(a.row0, bt.row1),
        },
        row1: Vec2 {
            x: dot(a.row1, bt.row0),
            y: dot(a.row1, bt.row1),
        },
    }
}

// ---------------------------------------------------------------------------
// Transpose
// ---------------------------------------------------------------------------

/// transpose(transpose(m)) ≡ m
pub proof fn lemma_transpose_involution<T: Ring>(m: Mat2x2<T>)
    ensures
        transpose(transpose(m)).row0.eqv(m.row0),
        transpose(transpose(m)).row1.eqv(m.row1),
{
    T::axiom_eqv_reflexive(m.row0.x);
    T::axiom_eqv_reflexive(m.row0.y);
    T::axiom_eqv_reflexive(m.row1.x);
    T::axiom_eqv_reflexive(m.row1.y);
}

// ---------------------------------------------------------------------------
// mat_vec_mul lemmas
// ---------------------------------------------------------------------------

/// mat_vec_mul(m, zero) ≡ zero
pub proof fn lemma_mat_vec_mul_zero<T: Ring>(m: Mat2x2<T>)
    ensures
        mat_vec_mul(m, Vec2 { x: T::zero(), y: T::zero() })
            .eqv(Vec2 { x: T::zero(), y: T::zero() }),
{
    crate::vec2::ops::lemma_dot_zero_right(m.row0);
    crate::vec2::ops::lemma_dot_zero_right(m.row1);
}

/// mat_vec_mul(m, a + b) ≡ mat_vec_mul(m, a) + mat_vec_mul(m, b)
pub proof fn lemma_mat_vec_mul_add<T: Ring>(m: Mat2x2<T>, a: Vec2<T>, b: Vec2<T>)
    ensures
        mat_vec_mul(m, a.add(b)).eqv(
            mat_vec_mul(m, a).add(mat_vec_mul(m, b))
        ),
{
    crate::vec2::ops::lemma_dot_distributes_right(m.row0, a, b);
    crate::vec2::ops::lemma_dot_distributes_right(m.row1, a, b);
}

/// mat_vec_mul(m, scale(s, v)) ≡ scale(s, mat_vec_mul(m, v))
pub proof fn lemma_mat_vec_mul_scale<T: Ring>(m: Mat2x2<T>, s: T, v: Vec2<T>)
    ensures
        mat_vec_mul(m, scale(s, v)).eqv(
            scale(s, mat_vec_mul(m, v))
        ),
{
    crate::vec2::ops::lemma_dot_scale_right(s, m.row0, v);
    crate::vec2::ops::lemma_dot_scale_right(s, m.row1, v);
}

// ---------------------------------------------------------------------------
// Basis-vector helpers
// ---------------------------------------------------------------------------

/// dot((1,0), v) ≡ v.x
proof fn lemma_dot_e0<T: Ring>(v: Vec2<T>)
    ensures
        dot(Vec2::<T> { x: T::one(), y: T::zero() }, v).eqv(v.x),
{
    // dot(e0, v) = 1*v.x + 0*v.y
    ring_lemmas::lemma_mul_one_left::<T>(v.x);
    ring_lemmas::lemma_mul_zero_left::<T>(v.y);

    // 1*v.x + 0*v.y ≡ v.x + 0 ≡ v.x
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().mul(v.x), v.x, T::zero().mul(v.y), T::zero(),
    );
    T::axiom_add_zero_right(v.x);
    T::axiom_eqv_transitive(
        dot(Vec2::<T> { x: T::one(), y: T::zero() }, v),
        v.x.add(T::zero()), v.x,
    );
}

/// dot((0,1), v) ≡ v.y
proof fn lemma_dot_e1<T: Ring>(v: Vec2<T>)
    ensures
        dot(Vec2::<T> { x: T::zero(), y: T::one() }, v).eqv(v.y),
{
    ring_lemmas::lemma_mul_zero_left::<T>(v.x);
    ring_lemmas::lemma_mul_one_left::<T>(v.y);

    // 0*v.x + 1*v.y ≡ 0 + v.y ≡ v.y
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(v.x), T::zero(), T::one().mul(v.y), v.y,
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(v.y);
    T::axiom_eqv_transitive(
        dot(Vec2::<T> { x: T::zero(), y: T::one() }, v),
        T::zero().add(v.y), v.y,
    );
}

proof fn lemma_dot_e0_right<T: Ring>(v: Vec2<T>)
    ensures
        dot(v, Vec2::<T> { x: T::one(), y: T::zero() }).eqv(v.x),
{
    let e0 = Vec2::<T> { x: T::one(), y: T::zero() };
    crate::vec2::ops::lemma_dot_commutative(v, e0);
    lemma_dot_e0(v);
    T::axiom_eqv_transitive(dot(v, e0), dot(e0, v), v.x);
}

proof fn lemma_dot_e1_right<T: Ring>(v: Vec2<T>)
    ensures
        dot(v, Vec2::<T> { x: T::zero(), y: T::one() }).eqv(v.y),
{
    let e1 = Vec2::<T> { x: T::zero(), y: T::one() };
    crate::vec2::ops::lemma_dot_commutative(v, e1);
    lemma_dot_e1(v);
    T::axiom_eqv_transitive(dot(v, e1), dot(e1, v), v.y);
}

// ---------------------------------------------------------------------------
// Identity lemmas
// ---------------------------------------------------------------------------

/// mat_vec_mul(identity(), v) ≡ v
pub proof fn lemma_identity_mul_vec<T: Ring>(v: Vec2<T>)
    ensures
        mat_vec_mul(identity(), v).eqv(v),
{
    lemma_dot_e0(v);
    lemma_dot_e1(v);
}

/// mat_mul(identity(), m).row_i ≡ m.row_i
pub proof fn lemma_identity_mat_mul_left<T: Ring>(m: Mat2x2<T>)
    ensures
        mat_mul(identity(), m).row0.eqv(m.row0),
        mat_mul(identity(), m).row1.eqv(m.row1),
{
    let bt = transpose(m);
    // Row 0: dot(e0, bt.row_j) ≡ bt.row_j.x = m.row0.{x,y}
    lemma_dot_e0(bt.row0);
    lemma_dot_e0(bt.row1);
    // Row 1: dot(e1, bt.row_j) ≡ bt.row_j.y = m.row1.{x,y}
    lemma_dot_e1(bt.row0);
    lemma_dot_e1(bt.row1);
}

/// mat_mul(m, identity()).row_i ≡ m.row_i
pub proof fn lemma_identity_mat_mul_right<T: Ring>(m: Mat2x2<T>)
    ensures
        mat_mul(m, identity()).row0.eqv(m.row0),
        mat_mul(m, identity()).row1.eqv(m.row1),
{
    // transpose(identity()) = identity(), so columns of I are e0, e1
    // dot(m.row_i, e_j) ≡ m.row_i.component_j
    lemma_dot_e0_right(m.row0);
    lemma_dot_e1_right(m.row0);
    lemma_dot_e0_right(m.row1);
    lemma_dot_e1_right(m.row1);
}

// ---------------------------------------------------------------------------
// Determinant lemmas
// ---------------------------------------------------------------------------

/// det(mᵀ) ≡ det(m)
pub proof fn lemma_det_transpose<T: Ring>(m: Mat2x2<T>)
    ensures
        det(transpose(m)).eqv(det(m)),
{
    // det(mᵀ) = mᵀ.row0.x * mᵀ.row1.y - mᵀ.row0.y * mᵀ.row1.x
    //         = m.row0.x * m.row1.y - m.row1.x * m.row0.y
    // det(m)  = m.row0.x * m.row1.y - m.row0.y * m.row1.x
    // Need: m.row1.x * m.row0.y ≡ m.row0.y * m.row1.x (commutativity)
    T::axiom_mul_commutative(m.row1.x, m.row0.y);
    // m.row0.x * m.row1.y is shared, reflexive
    T::axiom_eqv_reflexive(m.row0.x.mul(m.row1.y));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        m.row0.x.mul(m.row1.y), m.row0.x.mul(m.row1.y),
        m.row1.x.mul(m.row0.y), m.row0.y.mul(m.row1.x),
    );
}

/// det(swap rows) ≡ -det(m)
pub proof fn lemma_det_swap_rows<T: Ring>(m: Mat2x2<T>)
    ensures
        det(Mat2x2 { row0: m.row1, row1: m.row0 }).eqv(det(m).neg()),
{
    // det(swapped) = m.row1.x * m.row0.y - m.row1.y * m.row0.x
    // det(m)       = m.row0.x * m.row1.y - m.row0.y * m.row1.x
    // Need: det(swapped) ≡ -(det(m))
    // i.e. (m.row1.x * m.row0.y - m.row1.y * m.row0.x) ≡ -(m.row0.x * m.row1.y - m.row0.y * m.row1.x)

    // Step 1: Show det(swapped) ≡ m.row0.y * m.row1.x - m.row0.x * m.row1.y via commutativity
    T::axiom_mul_commutative(m.row1.x, m.row0.y);
    T::axiom_mul_commutative(m.row1.y, m.row0.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        m.row1.x.mul(m.row0.y), m.row0.y.mul(m.row1.x),
        m.row1.y.mul(m.row0.x), m.row0.x.mul(m.row1.y),
    );

    // Step 2: a - b ≡ -(b - a) via sub_antisymmetric
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(
        m.row0.y.mul(m.row1.x), m.row0.x.mul(m.row1.y),
    );

    // Chain: det(swapped) ≡ m.row0.y*m.row1.x - m.row0.x*m.row1.y ≡ -(m.row0.x*m.row1.y - m.row0.y*m.row1.x) = -det(m)
    T::axiom_eqv_transitive(
        det(Mat2x2 { row0: m.row1, row1: m.row0 }),
        m.row0.y.mul(m.row1.x).sub(m.row0.x.mul(m.row1.y)),
        m.row0.x.mul(m.row1.y).sub(m.row0.y.mul(m.row1.x)).neg(),
    );
}

/// det(AB) ≡ det(A)·det(B)
pub proof fn lemma_det_multiplicative<T: Ring>(a: Mat2x2<T>, b: Mat2x2<T>)
    ensures
        det(mat_mul(a, b)).eqv(det(a).mul(det(b))),
{
    // Let's name the entries
    let a00 = a.row0.x; let a01 = a.row0.y;
    let a10 = a.row1.x; let a11 = a.row1.y;
    let b00 = b.row0.x; let b01 = b.row0.y;
    let b10 = b.row1.x; let b11 = b.row1.y;

    // AB = mat_mul(a, b)
    // (AB)_00 = dot(a.row0, bt.row0) = a00*b00 + a01*b10
    // (AB)_01 = dot(a.row0, bt.row1) = a00*b01 + a01*b11
    // (AB)_10 = dot(a.row1, bt.row0) = a10*b00 + a11*b10
    // (AB)_11 = dot(a.row1, bt.row1) = a10*b01 + a11*b11

    // det(AB) = (a00*b00 + a01*b10)*(a10*b01 + a11*b11)
    //         - (a00*b01 + a01*b11)*(a10*b00 + a11*b10)

    // det(A)*det(B) = (a00*a11 - a01*a10)*(b00*b11 - b01*b10)

    // Both expand to: a00*a11*b00*b11 - a00*a11*b01*b10 - a01*a10*b00*b11 + a01*a10*b01*b10
    // det(AB) expands to the same after cancellation.

    // We'll prove this by expanding both sides and showing equality.

    // --- LHS: det(AB) ---
    // Expand (a00*b00 + a01*b10)*(a10*b01 + a11*b11)
    // = a00*b00*(a10*b01) + a00*b00*(a11*b11) + a01*b10*(a10*b01) + a01*b10*(a11*b11)
    let p = a00.mul(b00); // a00*b00
    let q = a01.mul(b10); // a01*b10
    let r = a10.mul(b01); // a10*b01
    let s = a11.mul(b11); // a11*b11

    let u = a00.mul(b01); // a00*b01
    let v = a01.mul(b11); // a01*b11
    let w = a10.mul(b00); // a10*b00
    let t = a11.mul(b10); // a11*b10

    // det(AB) = (p + q)*(r + s) - (u + v)*(w + t)
    // = p*r + p*s + q*r + q*s - (u*w + u*t + v*w + v*t)
    // = p*r + p*s + q*r + q*s - u*w - u*t - v*w - v*t

    // det(A)*det(B) = (a00*a11 - a01*a10)*(b00*b11 - b01*b10)
    // = a00*a11*b00*b11 - a00*a11*b01*b10 - a01*a10*b00*b11 + a01*a10*b01*b10

    // The key insight: both expand to the same 4-term expression.
    // p*s = (a00*b00)*(a11*b11) ≡ a00*(b00*a11)*b11 ≡ a00*(a11*b00)*b11 ≡ (a00*a11)*(b00*b11)
    // q*r = (a01*b10)*(a10*b01) ≡ (a01*a10)*(b10*b01) ≡ (a01*a10)*(b01*b10)
    // p*r = (a00*b00)*(a10*b01) ≡ (a00*a10)*(b00*b01)  -- will cancel with u*w
    // u*w = (a00*b01)*(a10*b00) ≡ (a00*a10)*(b01*b00) ≡ (a00*a10)*(b00*b01) -- same!
    // q*s = (a01*b10)*(a11*b11) ≡ (a01*a11)*(b10*b11)  -- will cancel with v*t
    // v*t = (a01*b11)*(a11*b10) ≡ (a01*a11)*(b11*b10) ≡ (a01*a11)*(b10*b11) -- same!
    // u*t = (a00*b01)*(a11*b10) ≡ (a00*a11)*(b01*b10)
    // v*w = (a01*b11)*(a10*b00) ≡ (a01*a10)*(b11*b00) ≡ (a01*a10)*(b00*b11)

    // So det(AB) = p*r + p*s + q*r + q*s - u*w - u*t - v*w - v*t
    //            = (p*r - u*w) + (q*s - v*t) + p*s + q*r - u*t - v*w
    //            = 0 + 0 + p*s - u*t - v*w + q*r
    //            = p*s - u*t + q*r - v*w   (after cancellations)
    //            = (a00*a11)*(b00*b11) - (a00*a11)*(b01*b10) + (a01*a10)*(b01*b10) - (a01*a10)*(b00*b11)
    //            = (a00*a11)*(b00*b11 - b01*b10) - (a01*a10)*(b00*b11 - b01*b10)
    //            = ((a00*a11) - (a01*a10))*(b00*b11 - b01*b10) = det(A)*det(B)

    // Strategy: Expand the LHS using ring distributivity, then show it equals RHS.

    // LHS = (p+q)*(r+s) - (u+v)*(w+t)
    // Expand (p+q)*(r+s) using distributivity:
    // (p+q)*(r+s) = p*(r+s) + q*(r+s) = p*r + p*s + q*r + q*s
    T::axiom_mul_distributes_left(p, r, s);     // p*(r+s) ≡ p*r + p*s
    T::axiom_mul_distributes_left(q, r, s);     // q*(r+s) ≡ q*r + q*s
    ring_lemmas::lemma_mul_distributes_right::<T>(p, q, r.add(s)); // (p+q)*(r+s) ≡ p*(r+s) + q*(r+s)

    // p*(r+s) + q*(r+s) ≡ (p*r + p*s) + (q*r + q*s)
    additive_group_lemmas::lemma_add_congruence::<T>(
        p.mul(r.add(s)), p.mul(r).add(p.mul(s)),
        q.mul(r.add(s)), q.mul(r).add(q.mul(s)),
    );
    // (p+q)*(r+s) ≡ (p*r + p*s) + (q*r + q*s)
    T::axiom_eqv_transitive(
        p.add(q).mul(r.add(s)),
        p.mul(r.add(s)).add(q.mul(r.add(s))),
        p.mul(r).add(p.mul(s)).add(q.mul(r).add(q.mul(s))),
    );

    // Similarly expand (u+v)*(w+t):
    T::axiom_mul_distributes_left(u, w, t);     // u*(w+t) ≡ u*w + u*t
    T::axiom_mul_distributes_left(v, w, t);     // v*(w+t) ≡ v*w + v*t
    ring_lemmas::lemma_mul_distributes_right::<T>(u, v, w.add(t)); // (u+v)*(w+t) ≡ u*(w+t) + v*(w+t)
    additive_group_lemmas::lemma_add_congruence::<T>(
        u.mul(w.add(t)), u.mul(w).add(u.mul(t)),
        v.mul(w.add(t)), v.mul(w).add(v.mul(t)),
    );
    T::axiom_eqv_transitive(
        u.add(v).mul(w.add(t)),
        u.mul(w.add(t)).add(v.mul(w.add(t))),
        u.mul(w).add(u.mul(t)).add(v.mul(w).add(v.mul(t))),
    );

    // Now LHS det(AB) = (p+q)*(r+s) - (u+v)*(w+t)
    // We have congruences for both factors.
    // det(AB) ≡ ((p*r + p*s) + (q*r + q*s)) - ((u*w + u*t) + (v*w + v*t))
    additive_group_lemmas::lemma_sub_congruence::<T>(
        p.add(q).mul(r.add(s)),
        p.mul(r).add(p.mul(s)).add(q.mul(r).add(q.mul(s))),
        u.add(v).mul(w.add(t)),
        u.mul(w).add(u.mul(t)).add(v.mul(w).add(v.mul(t))),
    );

    // Now show the cancellations.

    // Rearrange LHS expanded: (p*r + p*s + q*r + q*s) - (u*w + u*t + v*w + v*t)
    // Rearrange to: (p*r + p*s) + (q*r + q*s) rearranged as (p*r + q*r) + (p*s + q*s)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        p.mul(r), p.mul(s), q.mul(r), q.mul(s),
    );
    // Similarly: (u*w + u*t) + (v*w + v*t) rearranged as (u*w + v*w) + (u*t + v*t)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        u.mul(w), u.mul(t), v.mul(w), v.mul(t),
    );

    // Sub congruence with rearranged forms
    additive_group_lemmas::lemma_sub_congruence::<T>(
        p.mul(r).add(p.mul(s)).add(q.mul(r).add(q.mul(s))),
        p.mul(r).add(q.mul(r)).add(p.mul(s).add(q.mul(s))),
        u.mul(w).add(u.mul(t)).add(v.mul(w).add(v.mul(t))),
        u.mul(w).add(v.mul(w)).add(u.mul(t).add(v.mul(t))),
    );

    // Chain with previous
    T::axiom_eqv_transitive(
        det(mat_mul(a, b)),
        p.mul(r).add(p.mul(s)).add(q.mul(r).add(q.mul(s))).sub(
            u.mul(w).add(u.mul(t)).add(v.mul(w).add(v.mul(t)))
        ),
        p.mul(r).add(q.mul(r)).add(p.mul(s).add(q.mul(s))).sub(
            u.mul(w).add(v.mul(w)).add(u.mul(t).add(v.mul(t)))
        ),
    );

    // Now show p*r + q*r ≡ u*w + v*w (they cancel in the subtraction)
    // p*r = (a00*b00)*(a10*b01), u*w = (a00*b01)*(a10*b00)
    // p*r ≡ a00*(b00*a10)*b01 ≡ a00*(a10*b00)*b01 ≡ (a00*a10)*(b00*b01)
    // u*w ≡ a00*(b01*a10)*b00 ≡ a00*(a10*b01)*b00 ≡ (a00*a10)*(b01*b00) ≡ (a00*a10)*(b00*b01)
    // So p*r ≡ u*w.
    // p*r = (a00*b00)*(a10*b01)
    T::axiom_mul_associative(a00, b00, a10.mul(b01));
    T::axiom_eqv_symmetric(a00.mul(b00.mul(a10.mul(b01))), a00.mul(b00).mul(a10.mul(b01)));
    T::axiom_mul_commutative(b00, a10.mul(b01));
    ring_lemmas::lemma_mul_congruence_right::<T>(a00, b00.mul(a10.mul(b01)), a10.mul(b01).mul(b00));
    T::axiom_eqv_transitive(p.mul(r), a00.mul(b00.mul(a10.mul(b01))), a00.mul(a10.mul(b01).mul(b00)));
    T::axiom_mul_associative(a10, b01, b00);
    ring_lemmas::lemma_mul_congruence_right::<T>(a00, a10.mul(b01).mul(b00), a10.mul(b01.mul(b00)));
    T::axiom_eqv_transitive(p.mul(r), a00.mul(a10.mul(b01).mul(b00)), a00.mul(a10.mul(b01.mul(b00))));
    T::axiom_mul_associative(a00, a10, b01.mul(b00));
    T::axiom_eqv_symmetric(a00.mul(a10).mul(b01.mul(b00)), a00.mul(a10.mul(b01.mul(b00))));
    T::axiom_eqv_transitive(p.mul(r), a00.mul(a10.mul(b01.mul(b00))), a00.mul(a10).mul(b01.mul(b00)));
    T::axiom_mul_commutative(b01, b00);
    ring_lemmas::lemma_mul_congruence_right::<T>(a00.mul(a10), b01.mul(b00), b00.mul(b01));
    T::axiom_eqv_transitive(p.mul(r), a00.mul(a10).mul(b01.mul(b00)), a00.mul(a10).mul(b00.mul(b01)));
    // So p*r ≡ (a00*a10)*(b00*b01)

    // u*w = (a00*b01)*(a10*b00)
    T::axiom_mul_associative(a00, b01, a10.mul(b00));
    T::axiom_eqv_symmetric(a00.mul(b01.mul(a10.mul(b00))), a00.mul(b01).mul(a10.mul(b00)));
    T::axiom_mul_commutative(b01, a10.mul(b00));
    ring_lemmas::lemma_mul_congruence_right::<T>(a00, b01.mul(a10.mul(b00)), a10.mul(b00).mul(b01));
    T::axiom_eqv_transitive(u.mul(w), a00.mul(b01.mul(a10.mul(b00))), a00.mul(a10.mul(b00).mul(b01)));
    T::axiom_mul_associative(a10, b00, b01);
    ring_lemmas::lemma_mul_congruence_right::<T>(a00, a10.mul(b00).mul(b01), a10.mul(b00.mul(b01)));
    T::axiom_eqv_transitive(u.mul(w), a00.mul(a10.mul(b00).mul(b01)), a00.mul(a10.mul(b00.mul(b01))));
    T::axiom_mul_associative(a00, a10, b00.mul(b01));
    T::axiom_eqv_symmetric(a00.mul(a10).mul(b00.mul(b01)), a00.mul(a10.mul(b00.mul(b01))));
    T::axiom_eqv_transitive(u.mul(w), a00.mul(a10.mul(b00.mul(b01))), a00.mul(a10).mul(b00.mul(b01)));
    // So u*w ≡ (a00*a10)*(b00*b01)

    // p*r ≡ u*w (transitivity)
    T::axiom_eqv_symmetric(u.mul(w), a00.mul(a10).mul(b00.mul(b01)));
    T::axiom_eqv_transitive(p.mul(r), a00.mul(a10).mul(b00.mul(b01)), u.mul(w));

    // Similarly: q*r ≡ v*w
    // q*r = (a01*b10)*(a10*b01) ≡ (a01*a10)*(b10*b01) ≡ (a01*a10)*(b01*b10)
    T::axiom_mul_associative(a01, b10, a10.mul(b01));
    T::axiom_eqv_symmetric(a01.mul(b10.mul(a10.mul(b01))), a01.mul(b10).mul(a10.mul(b01)));
    T::axiom_mul_commutative(b10, a10.mul(b01));
    ring_lemmas::lemma_mul_congruence_right::<T>(a01, b10.mul(a10.mul(b01)), a10.mul(b01).mul(b10));
    T::axiom_eqv_transitive(q.mul(r), a01.mul(b10.mul(a10.mul(b01))), a01.mul(a10.mul(b01).mul(b10)));
    T::axiom_mul_associative(a10, b01, b10);
    ring_lemmas::lemma_mul_congruence_right::<T>(a01, a10.mul(b01).mul(b10), a10.mul(b01.mul(b10)));
    T::axiom_eqv_transitive(q.mul(r), a01.mul(a10.mul(b01).mul(b10)), a01.mul(a10.mul(b01.mul(b10))));
    T::axiom_mul_associative(a01, a10, b01.mul(b10));
    T::axiom_eqv_symmetric(a01.mul(a10).mul(b01.mul(b10)), a01.mul(a10.mul(b01.mul(b10))));
    T::axiom_eqv_transitive(q.mul(r), a01.mul(a10.mul(b01.mul(b10))), a01.mul(a10).mul(b01.mul(b10)));
    // q*r ≡ (a01*a10)*(b01*b10)

    // v*w = (a01*b11)*(a10*b00) ≡ (a01*a10)*(b11*b00) ≡ (a01*a10)*(b00*b11)
    T::axiom_mul_associative(a01, b11, a10.mul(b00));
    T::axiom_eqv_symmetric(a01.mul(b11.mul(a10.mul(b00))), a01.mul(b11).mul(a10.mul(b00)));
    T::axiom_mul_commutative(b11, a10.mul(b00));
    ring_lemmas::lemma_mul_congruence_right::<T>(a01, b11.mul(a10.mul(b00)), a10.mul(b00).mul(b11));
    T::axiom_eqv_transitive(v.mul(w), a01.mul(b11.mul(a10.mul(b00))), a01.mul(a10.mul(b00).mul(b11)));
    T::axiom_mul_associative(a10, b00, b11);
    ring_lemmas::lemma_mul_congruence_right::<T>(a01, a10.mul(b00).mul(b11), a10.mul(b00.mul(b11)));
    T::axiom_eqv_transitive(v.mul(w), a01.mul(a10.mul(b00).mul(b11)), a01.mul(a10.mul(b00.mul(b11))));
    T::axiom_mul_associative(a01, a10, b00.mul(b11));
    T::axiom_eqv_symmetric(a01.mul(a10).mul(b00.mul(b11)), a01.mul(a10.mul(b00.mul(b11))));
    T::axiom_eqv_transitive(v.mul(w), a01.mul(a10.mul(b00.mul(b11))), a01.mul(a10).mul(b00.mul(b11)));
    // v*w ≡ (a01*a10)*(b00*b11)

    // Similarly: q*s ≡ v*t (both ≡ (a01*a11)*(b10*b11))
    // q*s = (a01*b10)*(a11*b11)
    T::axiom_mul_associative(a01, b10, a11.mul(b11));
    T::axiom_eqv_symmetric(a01.mul(b10.mul(a11.mul(b11))), a01.mul(b10).mul(a11.mul(b11)));
    T::axiom_mul_commutative(b10, a11.mul(b11));
    ring_lemmas::lemma_mul_congruence_right::<T>(a01, b10.mul(a11.mul(b11)), a11.mul(b11).mul(b10));
    T::axiom_eqv_transitive(q.mul(s), a01.mul(b10.mul(a11.mul(b11))), a01.mul(a11.mul(b11).mul(b10)));
    T::axiom_mul_associative(a11, b11, b10);
    ring_lemmas::lemma_mul_congruence_right::<T>(a01, a11.mul(b11).mul(b10), a11.mul(b11.mul(b10)));
    T::axiom_eqv_transitive(q.mul(s), a01.mul(a11.mul(b11).mul(b10)), a01.mul(a11.mul(b11.mul(b10))));
    T::axiom_mul_associative(a01, a11, b11.mul(b10));
    T::axiom_eqv_symmetric(a01.mul(a11).mul(b11.mul(b10)), a01.mul(a11.mul(b11.mul(b10))));
    T::axiom_eqv_transitive(q.mul(s), a01.mul(a11.mul(b11.mul(b10))), a01.mul(a11).mul(b11.mul(b10)));
    T::axiom_mul_commutative(b11, b10);
    ring_lemmas::lemma_mul_congruence_right::<T>(a01.mul(a11), b11.mul(b10), b10.mul(b11));
    T::axiom_eqv_transitive(q.mul(s), a01.mul(a11).mul(b11.mul(b10)), a01.mul(a11).mul(b10.mul(b11)));
    // q*s ≡ (a01*a11)*(b10*b11)

    // v*t = (a01*b11)*(a11*b10)
    T::axiom_mul_associative(a01, b11, a11.mul(b10));
    T::axiom_eqv_symmetric(a01.mul(b11.mul(a11.mul(b10))), a01.mul(b11).mul(a11.mul(b10)));
    T::axiom_mul_commutative(b11, a11.mul(b10));
    ring_lemmas::lemma_mul_congruence_right::<T>(a01, b11.mul(a11.mul(b10)), a11.mul(b10).mul(b11));
    T::axiom_eqv_transitive(v.mul(t), a01.mul(b11.mul(a11.mul(b10))), a01.mul(a11.mul(b10).mul(b11)));
    T::axiom_mul_associative(a11, b10, b11);
    ring_lemmas::lemma_mul_congruence_right::<T>(a01, a11.mul(b10).mul(b11), a11.mul(b10.mul(b11)));
    T::axiom_eqv_transitive(v.mul(t), a01.mul(a11.mul(b10).mul(b11)), a01.mul(a11.mul(b10.mul(b11))));
    T::axiom_mul_associative(a01, a11, b10.mul(b11));
    T::axiom_eqv_symmetric(a01.mul(a11).mul(b10.mul(b11)), a01.mul(a11.mul(b10.mul(b11))));
    T::axiom_eqv_transitive(v.mul(t), a01.mul(a11.mul(b10.mul(b11))), a01.mul(a11).mul(b10.mul(b11)));
    // v*t ≡ (a01*a11)*(b10*b11)

    // q*s ≡ v*t
    T::axiom_eqv_symmetric(v.mul(t), a01.mul(a11).mul(b10.mul(b11)));
    T::axiom_eqv_transitive(q.mul(s), a01.mul(a11).mul(b10.mul(b11)), v.mul(t));

    // Now: p*r + q*r ≡ u*w + v*w (from p*r ≡ u*w and q*r ≡ v*w... wait, q*r and v*w are different)
    // Let me reconsider. We need to show that (p*r+q*r)+(p*s+q*s) - ((u*w+v*w)+(u*t+v*t)) ≡ det(A)*det(B)
    // We showed: p*r ≡ u*w, q*s ≡ v*t
    // So p*r + q*r ≡ u*w + q*r and u*w + v*w
    // Actually we need: p*r ≡ u*w  (shown above)
    // and q*s ≡ v*t (shown above)
    // So in (p*r + q*r) + (p*s + q*s) - (u*w + v*w) - (u*t + v*t):
    // p*r cancels u*w, q*s cancels v*t
    // Leaving: q*r + p*s - v*w - u*t

    // We need to show: q*r + p*s - v*w - u*t ≡ det(A)*det(B)
    // p*s ≡ (a00*a11)*(b00*b11), u*t ≡ (a00*a11)*(b01*b10)
    // q*r ≡ (a01*a10)*(b01*b10), v*w ≡ (a01*a10)*(b00*b11)

    // So q*r + p*s - v*w - u*t
    //    ≡ (a01*a10)*(b01*b10) + (a00*a11)*(b00*b11) - (a01*a10)*(b00*b11) - (a00*a11)*(b01*b10)
    //    = (a00*a11)*((b00*b11) - (b01*b10)) - (a01*a10)*((b00*b11) - (b01*b10))
    //    = ((a00*a11) - (a01*a10))*((b00*b11) - (b01*b10))
    //    = det(A)*det(B)

    // Let me now work with simpler names for the normalized forms.
    let aa = a00.mul(a11); // a00*a11
    let ab = a01.mul(a10); // a01*a10
    let bb = b00.mul(b11); // b00*b11
    let bc = b01.mul(b10); // b01*b10

    // We need to show p*s ≡ aa*bb
    // p*s = (a00*b00)*(a11*b11)
    T::axiom_mul_associative(a00, b00, a11.mul(b11));
    T::axiom_eqv_symmetric(a00.mul(b00.mul(a11.mul(b11))), p.mul(s));
    T::axiom_mul_commutative(b00, a11.mul(b11));
    ring_lemmas::lemma_mul_congruence_right::<T>(a00, b00.mul(a11.mul(b11)), a11.mul(b11).mul(b00));
    T::axiom_eqv_transitive(p.mul(s), a00.mul(b00.mul(a11.mul(b11))), a00.mul(a11.mul(b11).mul(b00)));
    T::axiom_mul_associative(a11, b11, b00);
    ring_lemmas::lemma_mul_congruence_right::<T>(a00, a11.mul(b11).mul(b00), a11.mul(b11.mul(b00)));
    T::axiom_eqv_transitive(p.mul(s), a00.mul(a11.mul(b11).mul(b00)), a00.mul(a11.mul(b11.mul(b00))));
    T::axiom_mul_commutative(b11, b00);
    ring_lemmas::lemma_mul_congruence_right::<T>(a11, b11.mul(b00), b00.mul(b11));
    ring_lemmas::lemma_mul_congruence_right::<T>(a00, a11.mul(b11.mul(b00)), a11.mul(bb));
    T::axiom_eqv_transitive(p.mul(s), a00.mul(a11.mul(b11.mul(b00))), a00.mul(a11.mul(bb)));
    T::axiom_mul_associative(a00, a11, bb);
    T::axiom_eqv_symmetric(aa.mul(bb), a00.mul(a11.mul(bb)));
    T::axiom_eqv_transitive(p.mul(s), a00.mul(a11.mul(bb)), aa.mul(bb));
    // p*s ≡ aa*bb

    // u*t ≡ aa*bc
    // u*t = (a00*b01)*(a11*b10)
    T::axiom_mul_associative(a00, b01, a11.mul(b10));
    T::axiom_eqv_symmetric(a00.mul(b01.mul(a11.mul(b10))), u.mul(t));
    T::axiom_mul_commutative(b01, a11.mul(b10));
    ring_lemmas::lemma_mul_congruence_right::<T>(a00, b01.mul(a11.mul(b10)), a11.mul(b10).mul(b01));
    T::axiom_eqv_transitive(u.mul(t), a00.mul(b01.mul(a11.mul(b10))), a00.mul(a11.mul(b10).mul(b01)));
    T::axiom_mul_associative(a11, b10, b01);
    ring_lemmas::lemma_mul_congruence_right::<T>(a00, a11.mul(b10).mul(b01), a11.mul(b10.mul(b01)));
    T::axiom_eqv_transitive(u.mul(t), a00.mul(a11.mul(b10).mul(b01)), a00.mul(a11.mul(b10.mul(b01))));
    T::axiom_mul_commutative(b10, b01);
    ring_lemmas::lemma_mul_congruence_right::<T>(a11, b10.mul(b01), bc);
    ring_lemmas::lemma_mul_congruence_right::<T>(a00, a11.mul(b10.mul(b01)), a11.mul(bc));
    T::axiom_eqv_transitive(u.mul(t), a00.mul(a11.mul(b10.mul(b01))), a00.mul(a11.mul(bc)));
    T::axiom_mul_associative(a00, a11, bc);
    T::axiom_eqv_symmetric(aa.mul(bc), a00.mul(a11.mul(bc)));
    T::axiom_eqv_transitive(u.mul(t), a00.mul(a11.mul(bc)), aa.mul(bc));
    // u*t ≡ aa*bc

    // q*r ≡ ab*bc (already shown above: q*r ≡ (a01*a10)*(b01*b10) = ab*bc)
    // Just confirmed: q*r ≡ a01.mul(a10).mul(b01.mul(b10)) = ab.mul(bc)
    // (already have this from above)

    // v*w ≡ ab*bb
    // (already shown above: v*w ≡ (a01*a10)*(b00*b11) = ab*bb)

    // Now we need:
    // (p*r + q*r) + (p*s + q*s) - ((u*w + v*w) + (u*t + v*t))
    // Using p*r ≡ u*w:
    //   p*r + q*r ≡ u*w + q*r
    T::axiom_eqv_reflexive(q.mul(r));
    additive_group_lemmas::lemma_add_congruence::<T>(p.mul(r), u.mul(w), q.mul(r), q.mul(r));

    // Using q*s ≡ v*t:
    //   p*s + q*s ≡ p*s + v*t
    T::axiom_eqv_reflexive(p.mul(s));
    additive_group_lemmas::lemma_add_congruence::<T>(p.mul(s), p.mul(s), q.mul(s), v.mul(t));

    // Combine: (p*r + q*r) + (p*s + q*s) ≡ (u*w + q*r) + (p*s + v*t)
    additive_group_lemmas::lemma_add_congruence::<T>(
        p.mul(r).add(q.mul(r)), u.mul(w).add(q.mul(r)),
        p.mul(s).add(q.mul(s)), p.mul(s).add(v.mul(t)),
    );

    // Also, u*w + v*w and u*t + v*t remain as-is on the subtrahend.
    // (u*w + v*w) + (u*t + v*t)
    // Rearrange numerator: (u*w + q*r) + (p*s + v*t) to (u*w + p*s) + (q*r + v*t)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        u.mul(w), q.mul(r), p.mul(s), v.mul(t),
    );

    // Chain: (p*r+q*r)+(p*s+q*s) ≡ (u*w+q*r)+(p*s+v*t) ≡ (u*w+p*s)+(q*r+v*t)
    T::axiom_eqv_transitive(
        p.mul(r).add(q.mul(r)).add(p.mul(s).add(q.mul(s))),
        u.mul(w).add(q.mul(r)).add(p.mul(s).add(v.mul(t))),
        u.mul(w).add(p.mul(s)).add(q.mul(r).add(v.mul(t))),
    );

    // Rearrange subtrahend: (u*w + v*w) + (u*t + v*t) to (u*w + u*t) + (v*w + v*t)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        u.mul(w), v.mul(w), u.mul(t), v.mul(t),
    );

    // Sub congruence
    additive_group_lemmas::lemma_sub_congruence::<T>(
        p.mul(r).add(q.mul(r)).add(p.mul(s).add(q.mul(s))),
        u.mul(w).add(p.mul(s)).add(q.mul(r).add(v.mul(t))),
        u.mul(w).add(v.mul(w)).add(u.mul(t).add(v.mul(t))),
        u.mul(w).add(u.mul(t)).add(v.mul(w).add(v.mul(t))),
    );

    // Chain with det(AB)
    T::axiom_eqv_transitive(
        det(mat_mul(a, b)),
        p.mul(r).add(q.mul(r)).add(p.mul(s).add(q.mul(s))).sub(
            u.mul(w).add(v.mul(w)).add(u.mul(t).add(v.mul(t)))
        ),
        u.mul(w).add(p.mul(s)).add(q.mul(r).add(v.mul(t))).sub(
            u.mul(w).add(u.mul(t)).add(v.mul(w).add(v.mul(t)))
        ),
    );

    // Now: (X + Y) - (X + Z) ≡ Y - Z where X = u*w, Y = p*s, Z = u*t; and (q*r+v*t) and (v*w+v*t)
    // Actually let me take a different approach. Use the normalized forms.
    // We have:
    //   p*s ≡ aa*bb, u*t ≡ aa*bc, q*r ≡ ab*bc, v*w ≡ ab*bb
    // So the numerator ≡ (u*w + aa*bb) + (ab*bc + v*t) and subtrahend ≡ (u*w + u*t) + (v*w + v*t)
    // This is getting complex. Let me switch to a cleaner approach.

    // Alternative cleaner approach: show det(AB) ≡ p*s + q*r - u*t - v*w
    // and det(A)*det(B) ≡ aa*bb - aa*bc - ab*bb + ab*bc
    // Then show these are equal via the normalized forms.

    // Actually, let me restart with a cleaner strategy.
    // Use the fact that (p+q)*(r+s) - (u+v)*(w+t)
    //   = p*r + p*s + q*r + q*s - u*w - u*t - v*w - v*t
    // and p*r = u*w, q*s = v*t, so the expression simplifies to p*s + q*r - u*t - v*w.
    // And det(A)*det(B) = (aa - ab)*(bb - bc) = aa*bb - aa*bc - ab*bb + ab*bc
    // = p*s - u*t - v*w + q*r (using our normalized forms).
    // So they match!

    // Let's prove: det(AB) ≡ p*s + q*r - u*t - v*w ≡ det(A)*det(B).

    // We already showed p*s ≡ aa*bb, u*t ≡ aa*bc, q*r ≡ ab*bc, v*w ≡ ab*bb.
    // Use these to replace in p*s + q*r - u*t - v*w:
    additive_group_lemmas::lemma_add_congruence::<T>(
        p.mul(s), aa.mul(bb), q.mul(r), ab.mul(bc),
    );

    additive_group_lemmas::lemma_add_congruence::<T>(
        u.mul(t), aa.mul(bc), v.mul(w), ab.mul(bb),
    );

    // p*s + q*r ≡ aa*bb + ab*bc
    // u*t + v*w ≡ aa*bc + ab*bb
    // (p*s + q*r) - (u*t + v*w) ≡ (aa*bb + ab*bc) - (aa*bc + ab*bb)
    additive_group_lemmas::lemma_sub_congruence::<T>(
        p.mul(s).add(q.mul(r)), aa.mul(bb).add(ab.mul(bc)),
        u.mul(t).add(v.mul(w)), aa.mul(bc).add(ab.mul(bb)),
    );

    // Now show (aa*bb + ab*bc) - (aa*bc + ab*bb) ≡ (aa - ab)*(bb - bc) = det(A)*det(B)
    // (aa - ab)*(bb - bc) ≡ aa*(bb-bc) - ab*(bb-bc)   [distributes_right]
    // = aa*bb - aa*bc - ab*bb + ab*bc
    // = (aa*bb + ab*bc) - (aa*bc + ab*bb)  [rearranging]
    ring_lemmas::lemma_sub_mul_right::<T>(aa, ab, bb.sub(bc));
    // (aa - ab)*(bb - bc) ≡ aa*(bb-bc) - ab*(bb-bc)

    ring_lemmas::lemma_mul_distributes_over_sub::<T>(aa, bb, bc);
    // aa*(bb - bc) ≡ aa*bb - aa*bc

    ring_lemmas::lemma_mul_distributes_over_sub::<T>(ab, bb, bc);
    // ab*(bb - bc) ≡ ab*bb - ab*bc

    // aa*(bb-bc) - ab*(bb-bc) ≡ (aa*bb - aa*bc) - (ab*bb - ab*bc)
    additive_group_lemmas::lemma_sub_congruence::<T>(
        aa.mul(bb.sub(bc)), aa.mul(bb).sub(aa.mul(bc)),
        ab.mul(bb.sub(bc)), ab.mul(bb).sub(ab.mul(bc)),
    );

    T::axiom_eqv_transitive(
        aa.sub(ab).mul(bb.sub(bc)),
        aa.mul(bb.sub(bc)).sub(ab.mul(bb.sub(bc))),
        aa.mul(bb).sub(aa.mul(bc)).sub(ab.mul(bb).sub(ab.mul(bc))),
    );

    // Now show (aa*bb - aa*bc) - (ab*bb - ab*bc)
    //        ≡ (aa*bb + ab*bc) - (aa*bc + ab*bb)
    // (A - B) - (C - D) = A - B - C + D = (A + D) - (B + C)

    // (aa*bb - aa*bc) ≡ aa*bb + (-(aa*bc))
    T::axiom_sub_is_add_neg(aa.mul(bb), aa.mul(bc));
    // (ab*bb - ab*bc) ≡ ab*bb + (-(ab*bc))
    T::axiom_sub_is_add_neg(ab.mul(bb), ab.mul(bc));

    // (aa*bb + (-(aa*bc))) - (ab*bb + (-(ab*bc)))
    // ≡ (aa*bb + (-(aa*bc))) + (-(ab*bb + (-(ab*bc))))
    T::axiom_sub_is_add_neg(
        aa.mul(bb).add(aa.mul(bc).neg()),
        ab.mul(bb).add(ab.mul(bc).neg()),
    );

    // Sub congruence to get (aa*bb - aa*bc) - (ab*bb - ab*bc)
    //                     ≡ (aa*bb + (-aa*bc)) - (ab*bb + (-ab*bc))
    additive_group_lemmas::lemma_sub_congruence::<T>(
        aa.mul(bb).sub(aa.mul(bc)),
        aa.mul(bb).add(aa.mul(bc).neg()),
        ab.mul(bb).sub(ab.mul(bc)),
        ab.mul(bb).add(ab.mul(bc).neg()),
    );

    // -(ab*bb + (-ab*bc)) ≡ (-ab*bb) + (-(-ab*bc)) ≡ (-ab*bb) + ab*bc
    additive_group_lemmas::lemma_neg_add::<T>(ab.mul(bb), ab.mul(bc).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(ab.mul(bc));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        ab.mul(bb).neg(),
        ab.mul(bc).neg().neg(), ab.mul(bc),
    );
    T::axiom_eqv_transitive(
        ab.mul(bb).add(ab.mul(bc).neg()).neg(),
        ab.mul(bb).neg().add(ab.mul(bc).neg().neg()),
        ab.mul(bb).neg().add(ab.mul(bc)),
    );

    // (aa*bb + (-aa*bc)) + Y.neg() ≡ (aa*bb + (-aa*bc)) + ((-ab*bb) + ab*bc)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        aa.mul(bb).add(aa.mul(bc).neg()),
        ab.mul(bb).add(ab.mul(bc).neg()).neg(),
        ab.mul(bb).neg().add(ab.mul(bc)),
    );

    // Chain: X - Y ≡ X + Y.neg() ≡ X + Z  (where Z = (-ab*bb) + ab*bc)
    T::axiom_eqv_transitive(
        aa.mul(bb).add(aa.mul(bc).neg()).sub(ab.mul(bb).add(ab.mul(bc).neg())),
        aa.mul(bb).add(aa.mul(bc).neg()).add(ab.mul(bb).add(ab.mul(bc).neg()).neg()),
        aa.mul(bb).add(aa.mul(bc).neg()).add(ab.mul(bb).neg().add(ab.mul(bc))),
    );

    // Chain: (aa*bb - aa*bc) - (ab*bb - ab*bc) ≡ X - Y ≡ X + Z
    T::axiom_eqv_transitive(
        aa.mul(bb).sub(aa.mul(bc)).sub(ab.mul(bb).sub(ab.mul(bc))),
        aa.mul(bb).add(aa.mul(bc).neg()).sub(ab.mul(bb).add(ab.mul(bc).neg())),
        aa.mul(bb).add(aa.mul(bc).neg()).add(ab.mul(bb).neg().add(ab.mul(bc))),
    );

    // Rearrange: (aa*bb + (-aa*bc)) + ((-ab*bb) + ab*bc)
    //          ≡ (aa*bb + ab*bc) + ((-aa*bc) + (-ab*bb))
    // First commute inner pair: (-ab*bb) + ab*bc ≡ ab*bc + (-ab*bb)
    T::axiom_add_commutative(ab.mul(bb).neg(), ab.mul(bc));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        aa.mul(bb).add(aa.mul(bc).neg()),
        ab.mul(bb).neg().add(ab.mul(bc)),
        ab.mul(bc).add(ab.mul(bb).neg()),
    );
    // Now rearrange: (aa*bb + (-aa*bc)) + (ab*bc + (-ab*bb))
    //             ≡ (aa*bb + ab*bc) + ((-aa*bc) + (-ab*bb))
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        aa.mul(bb), aa.mul(bc).neg(), ab.mul(bc), ab.mul(bb).neg(),
    );
    // Chain the rearrangement steps
    T::axiom_eqv_transitive(
        aa.mul(bb).add(aa.mul(bc).neg()).add(ab.mul(bb).neg().add(ab.mul(bc))),
        aa.mul(bb).add(aa.mul(bc).neg()).add(ab.mul(bc).add(ab.mul(bb).neg())),
        aa.mul(bb).add(ab.mul(bc)).add(aa.mul(bc).neg().add(ab.mul(bb).neg())),
    );

    // Chain with the main expression
    T::axiom_eqv_transitive(
        aa.mul(bb).sub(aa.mul(bc)).sub(ab.mul(bb).sub(ab.mul(bc))),
        aa.mul(bb).add(aa.mul(bc).neg()).add(ab.mul(bb).neg().add(ab.mul(bc))),
        aa.mul(bb).add(ab.mul(bc)).add(aa.mul(bc).neg().add(ab.mul(bb).neg())),
    );

    // (-aa*bc) + (-ab*bb) ≡ -(aa*bc + ab*bb)
    additive_group_lemmas::lemma_neg_add::<T>(aa.mul(bc), ab.mul(bb));
    T::axiom_eqv_symmetric(
        aa.mul(bc).add(ab.mul(bb)).neg(),
        aa.mul(bc).neg().add(ab.mul(bb).neg()),
    );

    additive_group_lemmas::lemma_add_congruence_right::<T>(
        aa.mul(bb).add(ab.mul(bc)),
        aa.mul(bc).neg().add(ab.mul(bb).neg()),
        aa.mul(bc).add(ab.mul(bb)).neg(),
    );

    T::axiom_eqv_transitive(
        aa.mul(bb).sub(aa.mul(bc)).sub(ab.mul(bb).sub(ab.mul(bc))),
        aa.mul(bb).add(ab.mul(bc)).add(aa.mul(bc).neg().add(ab.mul(bb).neg())),
        aa.mul(bb).add(ab.mul(bc)).add(aa.mul(bc).add(ab.mul(bb)).neg()),
    );

    // (aa*bb + ab*bc) + (-(aa*bc + ab*bb)) ≡ (aa*bb + ab*bc) - (aa*bc + ab*bb)
    T::axiom_sub_is_add_neg(
        aa.mul(bb).add(ab.mul(bc)),
        aa.mul(bc).add(ab.mul(bb)),
    );
    T::axiom_eqv_symmetric(
        aa.mul(bb).add(ab.mul(bc)).sub(aa.mul(bc).add(ab.mul(bb))),
        aa.mul(bb).add(ab.mul(bc)).add(aa.mul(bc).add(ab.mul(bb)).neg()),
    );

    T::axiom_eqv_transitive(
        aa.mul(bb).sub(aa.mul(bc)).sub(ab.mul(bb).sub(ab.mul(bc))),
        aa.mul(bb).add(ab.mul(bc)).add(aa.mul(bc).add(ab.mul(bb)).neg()),
        aa.mul(bb).add(ab.mul(bc)).sub(aa.mul(bc).add(ab.mul(bb))),
    );

    // det(A)*det(B) ≡ (aa*bb - aa*bc) - (ab*bb - ab*bc) ≡ (aa*bb + ab*bc) - (aa*bc + ab*bb)
    T::axiom_eqv_transitive(
        aa.sub(ab).mul(bb.sub(bc)),
        aa.mul(bb).sub(aa.mul(bc)).sub(ab.mul(bb).sub(ab.mul(bc))),
        aa.mul(bb).add(ab.mul(bc)).sub(aa.mul(bc).add(ab.mul(bb))),
    );

    // So: det(A)*det(B) ≡ (aa*bb + ab*bc) - (aa*bc + ab*bb)
    // And: (p*s + q*r) - (u*t + v*w) ≡ (aa*bb + ab*bc) - (aa*bc + ab*bb)  (shown above)
    // We still need to show det(AB) ≡ (p*s + q*r) - (u*t + v*w).

    // From line 633 we have:
    // det(AB) ≡ ((u*w+p*s)+(q*r+v*t)) - ((u*w+u*t)+(v*w+v*t))
    // Rearrange both sides to have common prefix X = u*w + v*t.

    // Rearrange numerator: (u*w+p*s)+(q*r+v*t) ≡ (u*w+v*t)+(p*s+q*r)
    // Step: commute q*r+v*t → v*t+q*r
    T::axiom_add_commutative(q.mul(r), v.mul(t));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        u.mul(w).add(p.mul(s)),
        q.mul(r).add(v.mul(t)),
        v.mul(t).add(q.mul(r)),
    );
    // Step: rearrange_2x2(u*w, p*s, v*t, q*r) → (u*w+v*t)+(p*s+q*r)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        u.mul(w), p.mul(s), v.mul(t), q.mul(r),
    );
    T::axiom_eqv_transitive(
        u.mul(w).add(p.mul(s)).add(q.mul(r).add(v.mul(t))),
        u.mul(w).add(p.mul(s)).add(v.mul(t).add(q.mul(r))),
        u.mul(w).add(v.mul(t)).add(p.mul(s).add(q.mul(r))),
    );

    // Rearrange subtrahend: (u*w+u*t)+(v*w+v*t) ≡ (u*w+v*t)+(u*t+v*w)
    // Step: commute v*w+v*t → v*t+v*w
    T::axiom_add_commutative(v.mul(w), v.mul(t));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        u.mul(w).add(u.mul(t)),
        v.mul(w).add(v.mul(t)),
        v.mul(t).add(v.mul(w)),
    );
    // Step: rearrange_2x2(u*w, u*t, v*t, v*w) → (u*w+v*t)+(u*t+v*w)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        u.mul(w), u.mul(t), v.mul(t), v.mul(w),
    );
    T::axiom_eqv_transitive(
        u.mul(w).add(u.mul(t)).add(v.mul(w).add(v.mul(t))),
        u.mul(w).add(u.mul(t)).add(v.mul(t).add(v.mul(w))),
        u.mul(w).add(v.mul(t)).add(u.mul(t).add(v.mul(w))),
    );

    // Sub congruence: numerator and subtrahend both rearranged
    additive_group_lemmas::lemma_sub_congruence::<T>(
        u.mul(w).add(p.mul(s)).add(q.mul(r).add(v.mul(t))),
        u.mul(w).add(v.mul(t)).add(p.mul(s).add(q.mul(r))),
        u.mul(w).add(u.mul(t)).add(v.mul(w).add(v.mul(t))),
        u.mul(w).add(v.mul(t)).add(u.mul(t).add(v.mul(w))),
    );

    // Chain with det(AB)
    T::axiom_eqv_transitive(
        det(mat_mul(a, b)),
        u.mul(w).add(p.mul(s)).add(q.mul(r).add(v.mul(t))).sub(
            u.mul(w).add(u.mul(t)).add(v.mul(w).add(v.mul(t)))
        ),
        u.mul(w).add(v.mul(t)).add(p.mul(s).add(q.mul(r))).sub(
            u.mul(w).add(v.mul(t)).add(u.mul(t).add(v.mul(w)))
        ),
    );

    // Now use (X+Y)-(X+Z) ≡ Y-Z where X = u*w+v*t, Y = p*s+q*r, Z = u*t+v*w
    let x_val = u.mul(w).add(v.mul(t));
    let y_val = p.mul(s).add(q.mul(r));
    let z_val = u.mul(t).add(v.mul(w));

    // (X + Y) - (X + Z) ≡ (X + Y) + (-(X + Z))
    T::axiom_sub_is_add_neg(x_val.add(y_val), x_val.add(z_val));

    // -(X + Z) ≡ -X + -Z
    additive_group_lemmas::lemma_neg_add::<T>(x_val, z_val);

    additive_group_lemmas::lemma_add_congruence_right::<T>(
        x_val.add(y_val),
        x_val.add(z_val).neg(),
        x_val.neg().add(z_val.neg()),
    );
    T::axiom_eqv_transitive(
        x_val.add(y_val).sub(x_val.add(z_val)),
        x_val.add(y_val).add(x_val.add(z_val).neg()),
        x_val.add(y_val).add(x_val.neg().add(z_val.neg())),
    );

    // Rearrange: (X + Y) + (-X + -Z) ≡ (X + -X) + (Y + -Z)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        x_val, y_val, x_val.neg(), z_val.neg(),
    );
    T::axiom_eqv_transitive(
        x_val.add(y_val).sub(x_val.add(z_val)),
        x_val.add(y_val).add(x_val.neg().add(z_val.neg())),
        x_val.add(x_val.neg()).add(y_val.add(z_val.neg())),
    );

    // X + -X ≡ 0
    T::axiom_add_inverse_right(x_val);
    // Y + -Z ≡ Y - Z
    T::axiom_sub_is_add_neg(y_val, z_val);
    T::axiom_eqv_symmetric(y_val.sub(z_val), y_val.add(z_val.neg()));

    additive_group_lemmas::lemma_add_congruence::<T>(
        x_val.add(x_val.neg()), T::zero(),
        y_val.add(z_val.neg()), y_val.sub(z_val),
    );
    T::axiom_eqv_transitive(
        x_val.add(y_val).sub(x_val.add(z_val)),
        x_val.add(x_val.neg()).add(y_val.add(z_val.neg())),
        T::zero().add(y_val.sub(z_val)),
    );

    // 0 + (Y - Z) ≡ Y - Z
    additive_group_lemmas::lemma_add_zero_left::<T>(y_val.sub(z_val));
    T::axiom_eqv_transitive(
        x_val.add(y_val).sub(x_val.add(z_val)),
        T::zero().add(y_val.sub(z_val)),
        y_val.sub(z_val),
    );

    // det(AB) ≡ (X+Y)-(X+Z) ≡ Y-Z = (p*s + q*r) - (u*t + v*w)
    T::axiom_eqv_transitive(
        det(mat_mul(a, b)),
        x_val.add(y_val).sub(x_val.add(z_val)),
        y_val.sub(z_val),
    );

    // Chain: Y-Z ≡ (aa*bb+ab*bc)-(aa*bc+ab*bb) ≡ det(A)*det(B)
    T::axiom_eqv_symmetric(
        aa.sub(ab).mul(bb.sub(bc)),
        aa.mul(bb).add(ab.mul(bc)).sub(aa.mul(bc).add(ab.mul(bb))),
    );

    T::axiom_eqv_transitive(
        y_val.sub(z_val),
        aa.mul(bb).add(ab.mul(bc)).sub(aa.mul(bc).add(ab.mul(bb))),
        aa.sub(ab).mul(bb.sub(bc)),
    );

    // Final: det(AB) ≡ Y-Z ≡ det(A)*det(B)
    T::axiom_eqv_transitive(
        det(mat_mul(a, b)),
        y_val.sub(z_val),
        det(a).mul(det(b)),
    );
}

// ---------------------------------------------------------------------------
// Adjugate & Inverse (Phase 3.1)
// ---------------------------------------------------------------------------

pub open spec fn adjugate<T: Ring>(m: Mat2x2<T>) -> Mat2x2<T> {
    Mat2x2 {
        row0: Vec2 { x: m.row1.y, y: m.row0.y.neg() },
        row1: Vec2 { x: m.row1.x.neg(), y: m.row0.x },
    }
}

pub open spec fn inverse<T: Field>(m: Mat2x2<T>) -> Mat2x2<T> {
    let d_inv = det(m).recip();
    let adj = adjugate(m);
    Mat2x2 {
        row0: scale(d_inv, adj.row0),
        row1: scale(d_inv, adj.row1),
    }
}

// ---------------------------------------------------------------------------
// Step 4: lemma_det_identity
// ---------------------------------------------------------------------------

/// det(identity()) ≡ 1
pub proof fn lemma_det_identity<T: Ring>()
    ensures
        det(identity::<T>()).eqv(T::one()),
{
    // det(I) = 1*1 - 0*0
    // 1*1 ≡ 1
    T::axiom_mul_one_right(T::one());
    // 0*0 ≡ 0
    ring_lemmas::lemma_mul_zero_left::<T>(T::zero());
    // det(I) = 1*1 - 0*0 ≡ 1 - 0
    additive_group_lemmas::lemma_sub_congruence::<T>(
        T::one().mul(T::one()), T::one(),
        T::zero().mul(T::zero()), T::zero(),
    );
    // 1 - 0 ≡ 1
    T::axiom_sub_is_add_neg(T::one(), T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        T::one(), T::zero().neg(), T::zero(),
    );
    T::axiom_add_zero_right(T::one());
    T::axiom_eqv_transitive(
        T::one().sub(T::zero()),
        T::one().add(T::zero().neg()),
        T::one().add(T::zero()),
    );
    T::axiom_eqv_transitive(
        T::one().sub(T::zero()),
        T::one().add(T::zero()),
        T::one(),
    );
    // Chain: det(I) ≡ 1 - 0 ≡ 1
    T::axiom_eqv_transitive(
        det(identity::<T>()),
        T::one().sub(T::zero()),
        T::one(),
    );
}

// ---------------------------------------------------------------------------
// Step 5: lemma_det_congruence
// ---------------------------------------------------------------------------

/// Determinant respects row-wise equivalence
pub proof fn lemma_det_congruence<T: Ring>(a: Mat2x2<T>, b: Mat2x2<T>)
    requires
        a.row0.eqv(b.row0),
        a.row1.eqv(b.row1),
    ensures
        det(a).eqv(det(b)),
{
    // a00*a11 ≡ b00*b11
    ring_lemmas::lemma_mul_congruence::<T>(a.row0.x, b.row0.x, a.row1.y, b.row1.y);
    // a01*a10 ≡ b01*b10
    ring_lemmas::lemma_mul_congruence::<T>(a.row0.y, b.row0.y, a.row1.x, b.row1.x);
    // det(a) = a00*a11 - a01*a10 ≡ b00*b11 - b01*b10 = det(b)
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.row0.x.mul(a.row1.y), b.row0.x.mul(b.row1.y),
        a.row0.y.mul(a.row1.x), b.row0.y.mul(b.row1.x),
    );
}

// ---------------------------------------------------------------------------
// Step 6: lemma_mat_mul_adjugate_right (private)
// ---------------------------------------------------------------------------

/// m * adj(m) has diagonal det(m) and off-diagonal 0
proof fn lemma_mat_mul_adjugate_right<T: Ring>(m: Mat2x2<T>)
    ensures
        mat_mul(m, adjugate(m)).row0.eqv(Vec2 { x: det(m), y: T::zero() }),
        mat_mul(m, adjugate(m)).row1.eqv(Vec2 { x: T::zero(), y: det(m) }),
{
    let a = m.row0.x;
    let b = m.row0.y;
    let c = m.row1.x;
    let d = m.row1.y;
    let adj = adjugate(m);

    // adj = [[d, -b], [-c, a]]
    // transpose(adj) = [[d, -c], [-b, a]]
    let bt = transpose(adj);
    // bt.row0 = (d, -c), bt.row1 = (-b, a)

    // mat_mul(m, adj).row0.x = dot(m.row0, bt.row0) = a*d + b*(-c)
    // Need to show: a*d + b*(-c) ≡ a*d - b*c = det(m)
    ring_lemmas::lemma_mul_neg_right::<T>(b, c);
    // b*(-c) ≡ -(b*c)
    T::axiom_eqv_reflexive(a.mul(d));
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.mul(d), a.mul(d),
        b.mul(c.neg()), b.mul(c).neg(),
    );
    // a*d + b*(-c) ≡ a*d + (-(b*c))
    T::axiom_sub_is_add_neg(a.mul(d), b.mul(c));
    T::axiom_eqv_symmetric(a.mul(d).sub(b.mul(c)), a.mul(d).add(b.mul(c).neg()));
    T::axiom_eqv_transitive(
        dot(m.row0, bt.row0),
        a.mul(d).add(b.mul(c).neg()),
        a.mul(d).sub(b.mul(c)),
    );
    // dot(m.row0, bt.row0) ≡ det(m). Done for (0,0).

    // mat_mul(m, adj).row0.y = dot(m.row0, bt.row1) = a*(-b) + b*a
    // Need to show: a*(-b) + b*a ≡ 0
    ring_lemmas::lemma_mul_neg_right::<T>(a, b);
    // a*(-b) ≡ -(a*b)
    T::axiom_mul_commutative(b, a);
    // b*a ≡ a*b
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.mul(b.neg()), a.mul(b).neg(),
        b.mul(a), a.mul(b),
    );
    // a*(-b) + b*a ≡ -(a*b) + a*b
    additive_group_lemmas::lemma_add_inverse_left::<T>(a.mul(b));
    T::axiom_eqv_transitive(
        dot(m.row0, bt.row1),
        a.mul(b).neg().add(a.mul(b)),
        T::zero(),
    );
    // dot(m.row0, bt.row1) ≡ 0. Done for (0,1).

    // mat_mul(m, adj).row1.x = dot(m.row1, bt.row0) = c*d + d*(-c)
    // Need to show: c*d + d*(-c) ≡ 0
    ring_lemmas::lemma_mul_neg_right::<T>(d, c);
    // d*(-c) ≡ -(d*c)
    T::axiom_mul_commutative(c, d);
    // c*d ≡ d*c
    additive_group_lemmas::lemma_add_congruence::<T>(
        c.mul(d), d.mul(c),
        d.mul(c.neg()), d.mul(c).neg(),
    );
    // c*d + d*(-c) ≡ d*c + -(d*c) ≡ 0
    T::axiom_add_inverse_right(d.mul(c));
    T::axiom_eqv_transitive(
        dot(m.row1, bt.row0),
        d.mul(c).add(d.mul(c).neg()),
        T::zero(),
    );
    // dot(m.row1, bt.row0) ≡ 0. Done for (1,0).

    // mat_mul(m, adj).row1.y = dot(m.row1, bt.row1) = c*(-b) + d*a
    // Need to show: c*(-b) + d*a ≡ a*d - b*c = det(m)
    ring_lemmas::lemma_mul_neg_right::<T>(c, b);
    // c*(-b) ≡ -(c*b)
    T::axiom_eqv_reflexive(d.mul(a));
    additive_group_lemmas::lemma_add_congruence::<T>(
        c.mul(b.neg()), c.mul(b).neg(),
        d.mul(a), d.mul(a),
    );
    // c*(-b) + d*a ≡ -(c*b) + d*a
    // Commute to d*a + -(c*b)
    T::axiom_add_commutative(c.mul(b).neg(), d.mul(a));
    T::axiom_eqv_transitive(
        dot(m.row1, bt.row1),
        c.mul(b).neg().add(d.mul(a)),
        d.mul(a).add(c.mul(b).neg()),
    );
    // d*a + -(c*b) ≡ d*a - c*b
    T::axiom_sub_is_add_neg(d.mul(a), c.mul(b));
    T::axiom_eqv_symmetric(d.mul(a).sub(c.mul(b)), d.mul(a).add(c.mul(b).neg()));
    T::axiom_eqv_transitive(
        dot(m.row1, bt.row1),
        d.mul(a).add(c.mul(b).neg()),
        d.mul(a).sub(c.mul(b)),
    );
    // Now show d*a - c*b ≡ a*d - b*c = det(m)
    T::axiom_mul_commutative(d, a);
    T::axiom_mul_commutative(c, b);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        d.mul(a), a.mul(d),
        c.mul(b), b.mul(c),
    );
    T::axiom_eqv_transitive(
        dot(m.row1, bt.row1),
        d.mul(a).sub(c.mul(b)),
        a.mul(d).sub(b.mul(c)),
    );
    // dot(m.row1, bt.row1) ≡ det(m). Done for (1,1).
}

// ---------------------------------------------------------------------------
// Step 7: lemma_mat_mul_adjugate_left (private)
// ---------------------------------------------------------------------------

/// adj(m) * m has diagonal det(m) and off-diagonal 0
proof fn lemma_mat_mul_adjugate_left<T: Ring>(m: Mat2x2<T>)
    ensures
        mat_mul(adjugate(m), m).row0.eqv(Vec2 { x: det(m), y: T::zero() }),
        mat_mul(adjugate(m), m).row1.eqv(Vec2 { x: T::zero(), y: det(m) }),
{
    let a = m.row0.x;
    let b = m.row0.y;
    let c = m.row1.x;
    let d = m.row1.y;
    let adj = adjugate(m);

    // adj.row0 = (d, -b), adj.row1 = (-c, a)
    // transpose(m) = [[a, c], [b, d]]
    let bt = transpose(m);
    // bt.row0 = (a, c), bt.row1 = (b, d)

    // mat_mul(adj, m).row0.x = dot(adj.row0, bt.row0) = d*a + (-b)*c
    // Need to show: d*a + (-b)*c ≡ a*d - b*c = det(m)
    ring_lemmas::lemma_mul_neg_left::<T>(b, c);
    // (-b)*c ≡ -(b*c)
    T::axiom_eqv_reflexive(d.mul(a));
    additive_group_lemmas::lemma_add_congruence::<T>(
        d.mul(a), d.mul(a),
        b.neg().mul(c), b.mul(c).neg(),
    );
    // d*a + (-b)*c ≡ d*a + -(b*c) ≡ d*a - b*c
    T::axiom_sub_is_add_neg(d.mul(a), b.mul(c));
    T::axiom_eqv_symmetric(d.mul(a).sub(b.mul(c)), d.mul(a).add(b.mul(c).neg()));
    T::axiom_eqv_transitive(
        dot(adj.row0, bt.row0),
        d.mul(a).add(b.mul(c).neg()),
        d.mul(a).sub(b.mul(c)),
    );
    // d*a - b*c ≡ a*d - b*c = det(m) via commutativity of d*a
    T::axiom_mul_commutative(d, a);
    T::axiom_eqv_reflexive(b.mul(c));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        d.mul(a), a.mul(d),
        b.mul(c), b.mul(c),
    );
    T::axiom_eqv_transitive(
        dot(adj.row0, bt.row0),
        d.mul(a).sub(b.mul(c)),
        a.mul(d).sub(b.mul(c)),
    );

    // mat_mul(adj, m).row0.y = dot(adj.row0, bt.row1) = d*b + (-b)*d
    // Need: d*b + (-b)*d ≡ 0
    ring_lemmas::lemma_mul_neg_left::<T>(b, d);
    // (-b)*d ≡ -(b*d)
    T::axiom_mul_commutative(d, b);
    // d*b ≡ b*d
    additive_group_lemmas::lemma_add_congruence::<T>(
        d.mul(b), b.mul(d),
        b.neg().mul(d), b.mul(d).neg(),
    );
    T::axiom_add_inverse_right(b.mul(d));
    T::axiom_eqv_transitive(
        dot(adj.row0, bt.row1),
        b.mul(d).add(b.mul(d).neg()),
        T::zero(),
    );

    // mat_mul(adj, m).row1.x = dot(adj.row1, bt.row0) = (-c)*a + a*c
    // Need: (-c)*a + a*c ≡ 0
    ring_lemmas::lemma_mul_neg_left::<T>(c, a);
    // (-c)*a ≡ -(c*a)
    T::axiom_mul_commutative(c, a);
    // c*a ≡ a*c
    additive_group_lemmas::lemma_neg_congruence::<T>(c.mul(a), a.mul(c));
    // -(c*a) ≡ -(a*c)
    T::axiom_eqv_reflexive(a.mul(c));
    additive_group_lemmas::lemma_add_congruence::<T>(
        c.neg().mul(a), c.mul(a).neg(),
        a.mul(c), a.mul(c),
    );
    // c.neg().mul(a).add(a.mul(c)) ≡ c.mul(a).neg().add(a.mul(c))
    // Now go from c.mul(a).neg() to a.mul(c).neg() via neg_congruence
    additive_group_lemmas::lemma_add_congruence::<T>(
        c.mul(a).neg(), a.mul(c).neg(),
        a.mul(c), a.mul(c),
    );
    T::axiom_eqv_transitive(
        dot(adj.row1, bt.row0),
        c.mul(a).neg().add(a.mul(c)),
        a.mul(c).neg().add(a.mul(c)),
    );
    additive_group_lemmas::lemma_add_inverse_left::<T>(a.mul(c));
    T::axiom_eqv_transitive(
        dot(adj.row1, bt.row0),
        a.mul(c).neg().add(a.mul(c)),
        T::zero(),
    );

    // mat_mul(adj, m).row1.y = dot(adj.row1, bt.row1) = (-c)*b + a*d
    // Need: (-c)*b + a*d ≡ a*d - b*c = det(m)
    ring_lemmas::lemma_mul_neg_left::<T>(c, b);
    // (-c)*b ≡ -(c*b)
    T::axiom_eqv_reflexive(a.mul(d));
    additive_group_lemmas::lemma_add_congruence::<T>(
        c.neg().mul(b), c.mul(b).neg(),
        a.mul(d), a.mul(d),
    );
    // (-c)*b + a*d ≡ -(c*b) + a*d
    // Commute: ≡ a*d + -(c*b)
    T::axiom_add_commutative(c.mul(b).neg(), a.mul(d));
    T::axiom_eqv_transitive(
        dot(adj.row1, bt.row1),
        c.mul(b).neg().add(a.mul(d)),
        a.mul(d).add(c.mul(b).neg()),
    );
    // a*d + -(c*b) ≡ a*d - c*b
    T::axiom_sub_is_add_neg(a.mul(d), c.mul(b));
    T::axiom_eqv_symmetric(a.mul(d).sub(c.mul(b)), a.mul(d).add(c.mul(b).neg()));
    T::axiom_eqv_transitive(
        dot(adj.row1, bt.row1),
        a.mul(d).add(c.mul(b).neg()),
        a.mul(d).sub(c.mul(b)),
    );
    // a*d - c*b ≡ a*d - b*c = det(m) via commutativity c*b ≡ b*c
    T::axiom_mul_commutative(c, b);
    T::axiom_eqv_reflexive(a.mul(d));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.mul(d), a.mul(d),
        c.mul(b), b.mul(c),
    );
    T::axiom_eqv_transitive(
        dot(adj.row1, bt.row1),
        a.mul(d).sub(c.mul(b)),
        a.mul(d).sub(b.mul(c)),
    );
}

// ---------------------------------------------------------------------------
// Step 8: lemma_inverse_right (public)
// ---------------------------------------------------------------------------

/// m * inverse(m) ≡ identity() when det(m) ≢ 0
pub proof fn lemma_inverse_right<T: Field>(m: Mat2x2<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        mat_mul(m, inverse(m)).row0.eqv(identity::<T>().row0),
        mat_mul(m, inverse(m)).row1.eqv(identity::<T>().row1),
{
    let d = det(m);
    let d_inv = d.recip();
    let adj = adjugate(m);
    let inv = inverse(m);

    // inv = Mat2x2 { row0: scale(d_inv, adj.row0), row1: scale(d_inv, adj.row1) }

    // mat_mul(m, inv) entries are dot products of m's rows with transpose(inv) columns.
    // transpose(inv).row0 = (inv.row0.x, inv.row1.x) = (d_inv*adj.row0.x, d_inv*adj.row1.x)
    // transpose(inv).row1 = (inv.row0.y, inv.row1.y) = (d_inv*adj.row0.y, d_inv*adj.row1.y)
    // That is, transpose(inv) columns = scale(d_inv, transpose(adj) columns)

    // So mat_mul(m, inv).row0.x = dot(m.row0, transpose(inv).row0)
    //                           = dot(m.row0, scale(d_inv, transpose(adj).row0))
    //                           ≡ d_inv * dot(m.row0, transpose(adj).row0)   [dot_scale_right]
    //                           = d_inv * mat_mul(m, adj).row0.x
    //                           ≡ d_inv * det(m) = 1   [by mat_mul_adjugate_right and axiom_mul_recip]

    // The key insight: transpose(inv).row_j = scale(d_inv, transpose(adj).row_j)
    // because inv.row_i = scale(d_inv, adj.row_i) means component-wise,
    // inv.row_i.x = d_inv * adj.row_i.x, inv.row_i.y = d_inv * adj.row_i.y
    // So transpose(inv).row0 = (inv.row0.x, inv.row1.x) = (d_inv*adj.row0.x, d_inv*adj.row1.x)
    //                        = scale(d_inv, (adj.row0.x, adj.row1.x))
    //                        = scale(d_inv, transpose(adj).row0)

    // Step 1: Get the adjugate products
    lemma_mat_mul_adjugate_right(m);

    // Step 2: For each entry of mat_mul(m, inv), factor out d_inv using dot_scale_right

    // (0,0): dot(m.row0, transpose(inv).row0) ≡ d_inv * dot(m.row0, transpose(adj).row0)
    let t_inv = transpose(inv);
    let t_adj = transpose(adj);

    // Show: t_inv.row0 = scale(d_inv, t_adj.row0)
    // t_inv.row0 = (inv.row0.x, inv.row1.x) = (d_inv*adj.row0.x, d_inv*adj.row1.x)
    // t_adj.row0 = (adj.row0.x, adj.row1.x)
    // scale(d_inv, t_adj.row0) = (d_inv*adj.row0.x, d_inv*adj.row1.x) ✓ (definitionally equal)

    // Show: t_inv.row1 = scale(d_inv, t_adj.row1)
    // t_inv.row1 = (inv.row0.y, inv.row1.y) = (d_inv*adj.row0.y, d_inv*adj.row1.y)
    // t_adj.row1 = (adj.row0.y, adj.row1.y)
    // scale(d_inv, t_adj.row1) = (d_inv*adj.row0.y, d_inv*adj.row1.y) ✓ (definitionally equal)

    // Factor d_inv out of each dot product
    crate::vec2::ops::lemma_dot_scale_right(d_inv, m.row0, t_adj.row0);
    crate::vec2::ops::lemma_dot_scale_right(d_inv, m.row0, t_adj.row1);
    crate::vec2::ops::lemma_dot_scale_right(d_inv, m.row1, t_adj.row0);
    crate::vec2::ops::lemma_dot_scale_right(d_inv, m.row1, t_adj.row1);

    // Now: dot(m.row0, t_inv.row0) ≡ d_inv * dot(m.row0, t_adj.row0)
    //      = d_inv * mat_mul(m, adj).row0.x

    // From mat_mul_adjugate_right:
    // mat_mul(m, adj).row0.x ≡ det(m) = d
    // mat_mul(m, adj).row0.y ≡ 0
    // mat_mul(m, adj).row1.x ≡ 0
    // mat_mul(m, adj).row1.y ≡ det(m) = d

    // (0,0): d_inv * d ≡ 1
    // dot(m.row0, t_adj.row0) = mat_mul(m, adj).row0.x ≡ d
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row0, t_adj.row0), d);
    T::axiom_eqv_transitive(
        dot(m.row0, t_inv.row0),
        d_inv.mul(dot(m.row0, t_adj.row0)),
        d_inv.mul(d),
    );
    field_lemmas::lemma_mul_recip_left::<T>(d);
    T::axiom_eqv_transitive(
        dot(m.row0, t_inv.row0),
        d_inv.mul(d),
        T::one(),
    );

    // (0,1): d_inv * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row0, t_adj.row1), T::zero());
    T::axiom_eqv_transitive(
        dot(m.row0, t_inv.row1),
        d_inv.mul(dot(m.row0, t_adj.row1)),
        d_inv.mul(T::zero()),
    );
    T::axiom_mul_zero_right(d_inv);
    T::axiom_eqv_transitive(
        dot(m.row0, t_inv.row1),
        d_inv.mul(T::zero()),
        T::zero(),
    );

    // (1,0): d_inv * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row1, t_adj.row0), T::zero());
    T::axiom_eqv_transitive(
        dot(m.row1, t_inv.row0),
        d_inv.mul(dot(m.row1, t_adj.row0)),
        d_inv.mul(T::zero()),
    );
    T::axiom_mul_zero_right(d_inv);
    T::axiom_eqv_transitive(
        dot(m.row1, t_inv.row0),
        d_inv.mul(T::zero()),
        T::zero(),
    );

    // (1,1): d_inv * d ≡ 1
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(m.row1, t_adj.row1), d);
    T::axiom_eqv_transitive(
        dot(m.row1, t_inv.row1),
        d_inv.mul(dot(m.row1, t_adj.row1)),
        d_inv.mul(d),
    );
    field_lemmas::lemma_mul_recip_left::<T>(d);
    T::axiom_eqv_transitive(
        dot(m.row1, t_inv.row1),
        d_inv.mul(d),
        T::one(),
    );
}

// ---------------------------------------------------------------------------
// Step 9: lemma_inverse_left (public)
// ---------------------------------------------------------------------------

/// inverse(m) * m ≡ identity() when det(m) ≢ 0
pub proof fn lemma_inverse_left<T: Field>(m: Mat2x2<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        mat_mul(inverse(m), m).row0.eqv(identity::<T>().row0),
        mat_mul(inverse(m), m).row1.eqv(identity::<T>().row1),
{
    let d = det(m);
    let d_inv = d.recip();
    let adj = adjugate(m);
    let inv = inverse(m);

    // Get the adjugate products from the left
    lemma_mat_mul_adjugate_left(m);

    let t_m = transpose(m);

    // mat_mul(inv, m).row_i.j = dot(inv.row_i, t_m.row_j)
    //                         = dot(scale(d_inv, adj.row_i), t_m.row_j)
    //                         ≡ d_inv * dot(adj.row_i, t_m.row_j)   [dot_scale_left]
    //                         = d_inv * mat_mul(adj, m).row_i.j

    crate::vec2::ops::lemma_dot_scale_left(d_inv, adj.row0, t_m.row0);
    crate::vec2::ops::lemma_dot_scale_left(d_inv, adj.row0, t_m.row1);
    crate::vec2::ops::lemma_dot_scale_left(d_inv, adj.row1, t_m.row0);
    crate::vec2::ops::lemma_dot_scale_left(d_inv, adj.row1, t_m.row1);

    // From mat_mul_adjugate_left:
    // mat_mul(adj, m).row0.x ≡ d, mat_mul(adj, m).row0.y ≡ 0
    // mat_mul(adj, m).row1.x ≡ 0, mat_mul(adj, m).row1.y ≡ d

    // (0,0): d_inv * d ≡ 1
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row0, t_m.row0), d);
    T::axiom_eqv_transitive(
        dot(inv.row0, t_m.row0),
        d_inv.mul(dot(adj.row0, t_m.row0)),
        d_inv.mul(d),
    );
    field_lemmas::lemma_mul_recip_left::<T>(d);
    T::axiom_eqv_transitive(
        dot(inv.row0, t_m.row0),
        d_inv.mul(d),
        T::one(),
    );

    // (0,1): d_inv * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row0, t_m.row1), T::zero());
    T::axiom_eqv_transitive(
        dot(inv.row0, t_m.row1),
        d_inv.mul(dot(adj.row0, t_m.row1)),
        d_inv.mul(T::zero()),
    );
    T::axiom_mul_zero_right(d_inv);
    T::axiom_eqv_transitive(
        dot(inv.row0, t_m.row1),
        d_inv.mul(T::zero()),
        T::zero(),
    );

    // (1,0): d_inv * 0 ≡ 0
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row1, t_m.row0), T::zero());
    T::axiom_eqv_transitive(
        dot(inv.row1, t_m.row0),
        d_inv.mul(dot(adj.row1, t_m.row0)),
        d_inv.mul(T::zero()),
    );
    T::axiom_mul_zero_right(d_inv);
    T::axiom_eqv_transitive(
        dot(inv.row1, t_m.row0),
        d_inv.mul(T::zero()),
        T::zero(),
    );

    // (1,1): d_inv * d ≡ 1
    ring_lemmas::lemma_mul_congruence_right::<T>(d_inv, dot(adj.row1, t_m.row1), d);
    T::axiom_eqv_transitive(
        dot(inv.row1, t_m.row1),
        d_inv.mul(dot(adj.row1, t_m.row1)),
        d_inv.mul(d),
    );
    field_lemmas::lemma_mul_recip_left::<T>(d);
    T::axiom_eqv_transitive(
        dot(inv.row1, t_m.row1),
        d_inv.mul(d),
        T::one(),
    );
}

// ---------------------------------------------------------------------------
// Step 10: lemma_det_inverse (public)
// ---------------------------------------------------------------------------

/// det(inverse(m)) ≡ recip(det(m)) when det(m) ≢ 0
pub proof fn lemma_det_inverse<T: Field>(m: Mat2x2<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        det(inverse(m)).eqv(det(m).recip()),
{
    let d = det(m);
    let inv = inverse(m);

    // Step 1: mat_mul(m, inv) ≡ identity (row-wise)
    lemma_inverse_right(m);

    // Step 2: det(mat_mul(m, inv)) ≡ det(identity()) via det_congruence
    lemma_det_congruence(mat_mul(m, inv), identity::<T>());

    // Step 3: det(identity()) ≡ 1
    lemma_det_identity::<T>();

    // Step 4: det(mat_mul(m, inv)) ≡ 1
    T::axiom_eqv_transitive(
        det(mat_mul(m, inv)),
        det(identity::<T>()),
        T::one(),
    );

    // Step 5: det(mat_mul(m, inv)) ≡ det(m) * det(inv) via det_multiplicative
    lemma_det_multiplicative(m, inv);

    // Step 6: det(m) * det(inv) ≡ 1
    T::axiom_eqv_symmetric(det(mat_mul(m, inv)), d.mul(det(inv)));
    T::axiom_eqv_transitive(
        d.mul(det(inv)),
        det(mat_mul(m, inv)),
        T::one(),
    );

    // Step 7: By recip_unique, det(inv) ≡ recip(d)
    field_lemmas::lemma_recip_unique::<T>(d, det(inv));
}

// ---------------------------------------------------------------------------
// Step 11: lemma_inverse_involution (public)
// ---------------------------------------------------------------------------

/// inverse(inverse(m)) ≡ m when det(m) ≢ 0
pub proof fn lemma_inverse_involution<T: Field>(m: Mat2x2<T>)
    requires
        !det(m).eqv(T::zero()),
    ensures
        inverse(inverse(m)).row0.eqv(m.row0),
        inverse(inverse(m)).row1.eqv(m.row1),
{
    let d = det(m);
    let d_inv = d.recip();
    let inv = inverse(m);

    // Step 1: det(inv) ≡ recip(d)
    lemma_det_inverse(m);

    // Step 2: det(inv) ≢ 0 (since d ≢ 0 implies recip(d) ≢ 0)
    // We need to show !det(inv).eqv(T::zero()).
    // Since det(inv) ≡ recip(d) and d ≢ 0:
    // If recip(d) ≡ 0 then d * recip(d) ≡ d * 0 ≡ 0, but d * recip(d) ≡ 1.
    // 1 ≡ 0 is impossible (by Ring axiom). So recip(d) ≢ 0.
    // We prove this by contradiction structure.

    // Step 3: inverse(inv) = scale(recip(det(inv)), adjugate(inv))
    // We need to show this equals m.

    // adjugate(inv):
    // inv = Mat2x2 { row0: (d_inv*d11, d_inv*(-a01)), row1: (d_inv*(-a10), d_inv*a00) }
    // where a00 = m.row0.x, a01 = m.row0.y, a10 = m.row1.x, a11 = m.row1.y
    // adj(inv).row0 = (inv.row1.y, -(inv.row0.y)) = (d_inv*a00, -(d_inv*(-a01)))
    // adj(inv).row1 = (-(inv.row1.x), inv.row0.x) = (-(d_inv*(-a10)), d_inv*a11)

    // recip(det(inv)) ≡ recip(recip(d)) ≡ d (by recip_involution)

    // So inverse(inv).row0 = scale(recip(det(inv)), adj(inv).row0)
    //                      ≡ scale(d, (d_inv*a00, -(d_inv*(-a01))))

    // For component x: d * (d_inv * a00) ≡ (d * d_inv) * a00 ≡ 1 * a00 ≡ a00
    // For component y: d * (-(d_inv * (-a01))) ≡ d * (d_inv * a01) ≡ a01

    // Strategy: show each of the 4 components of inverse(inverse(m)) equals the
    // corresponding component of m.

    let a00 = m.row0.x;
    let a01 = m.row0.y;
    let a10 = m.row1.x;
    let a11 = m.row1.y;

    // Step 2a: Prove !det(inv).eqv(T::zero())
    // We know det(inv) ≡ d_inv = recip(d). If recip(d) ≡ 0, then
    // d * recip(d) ≡ d * 0 ≡ 0, but d * recip(d) ≡ 1, giving 1 ≡ 0. Contradiction.
    if d_inv.eqv(T::zero()) {
        ring_lemmas::lemma_mul_congruence_right::<T>(d, d_inv, T::zero());
        T::axiom_mul_zero_right(d);
        T::axiom_mul_recip_right(d);
        T::axiom_eqv_transitive(d.mul(d_inv), d.mul(T::zero()), T::zero());
        T::axiom_eqv_symmetric(d.mul(d_inv), T::one());
        T::axiom_eqv_transitive(T::one(), d.mul(d_inv), T::zero());
        T::axiom_one_ne_zero();
    }
    // So !d_inv.eqv(T::zero()), and since det(inv) ≡ d_inv:
    // if det(inv) ≡ 0, then d_inv ≡ det(inv) ≡ 0, contradiction
    if det(inv).eqv(T::zero()) {
        T::axiom_eqv_symmetric(det(inv), d_inv);
        T::axiom_eqv_transitive(d_inv, det(inv), T::zero());
    }

    // recip(det(inv)) ≡ d via recip_involution
    // First, det(inv) ≡ d_inv (from step 1)
    // recip(det(inv)) ≡ recip(d_inv) via recip_congruence
    T::axiom_recip_congruence(det(inv), d_inv);
    // recip(d_inv) ≡ d via recip_involution
    field_lemmas::lemma_recip_involution::<T>(d);
    let recip_det_inv = det(inv).recip();
    T::axiom_eqv_transitive(recip_det_inv, d_inv.recip(), d);

    // Now inverse(inv).row0 = scale(recip_det_inv, adjugate(inv).row0)
    // adjugate(inv).row0 = Vec2 { x: inv.row1.y, y: inv.row0.y.neg() }
    // inv.row1.y = d_inv * a00
    // inv.row0.y = d_inv * (-a01) = d_inv * a01.neg()
    // inv.row0.y.neg() = (d_inv * a01.neg()).neg()

    // inverse(inv).row0.x = recip_det_inv * inv.row1.y = recip_det_inv * (d_inv * a00)
    // ≡ d * (d_inv * a00) ≡ (d * d_inv) * a00 ≡ 1 * a00 ≡ a00

    // Show: recip_det_inv * (d_inv * a00) ≡ a00
    // recip_det_inv ≡ d, so recip_det_inv * (d_inv * a00) ≡ d * (d_inv * a00)
    T::axiom_mul_congruence_left(recip_det_inv, d, d_inv.mul(a00));
    // d * (d_inv * a00) ≡ (d * d_inv) * a00
    T::axiom_mul_associative(d, d_inv, a00);
    T::axiom_eqv_symmetric(d.mul(d_inv).mul(a00), d.mul(d_inv.mul(a00)));
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a00)),
        d.mul(d_inv.mul(a00)),
        d.mul(d_inv).mul(a00),
    );
    // d * d_inv ≡ 1
    T::axiom_mul_recip_right(d);
    T::axiom_mul_congruence_left(d.mul(d_inv), T::one(), a00);
    ring_lemmas::lemma_mul_one_left::<T>(a00);
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a00)),
        d.mul(d_inv).mul(a00),
        T::one().mul(a00),
    );
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a00)),
        T::one().mul(a00),
        a00,
    );

    // inverse(inv).row0.y = recip_det_inv * (-(d_inv * a01.neg()))
    // ≡ d * (-(d_inv * (-a01)))
    // -(d_inv * (-a01)) ≡ d_inv * a01 via neg(neg) inside
    // d_inv * (-a01).neg() ... let me think more carefully.

    // inv.row0.y = d_inv * a01.neg() (this is scale(d_inv, adj.row0).y where adj.row0.y = a01.neg())
    // adjugate(inv).row0.y = inv.row0.y.neg() = (d_inv * a01.neg()).neg()
    // (d_inv * a01.neg()).neg() ≡ -(d_inv * (-a01))
    // By mul_neg_right: d_inv * (-a01) ≡ -(d_inv * a01)
    // So -(d_inv * (-a01)) ≡ -(-(d_inv * a01)) ≡ d_inv * a01
    ring_lemmas::lemma_mul_neg_right::<T>(d_inv, a01);
    additive_group_lemmas::lemma_neg_congruence::<T>(d_inv.mul(a01.neg()), d_inv.mul(a01).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(d_inv.mul(a01));
    T::axiom_eqv_transitive(
        d_inv.mul(a01.neg()).neg(),
        d_inv.mul(a01).neg().neg(),
        d_inv.mul(a01),
    );
    // So adjugate(inv).row0.y ≡ d_inv * a01

    // inverse(inv).row0.y = recip_det_inv * adjugate(inv).row0.y
    //                     ≡ recip_det_inv * (d_inv * a01)
    // Same pattern: ≡ d * (d_inv * a01) ≡ a01
    ring_lemmas::lemma_mul_congruence_right::<T>(recip_det_inv, d_inv.mul(a01.neg()).neg(), d_inv.mul(a01));
    T::axiom_mul_congruence_left(recip_det_inv, d, d_inv.mul(a01));
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a01.neg()).neg()),
        recip_det_inv.mul(d_inv.mul(a01)),
        d.mul(d_inv.mul(a01)),
    );
    T::axiom_mul_associative(d, d_inv, a01);
    T::axiom_eqv_symmetric(d.mul(d_inv).mul(a01), d.mul(d_inv.mul(a01)));
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a01.neg()).neg()),
        d.mul(d_inv.mul(a01)),
        d.mul(d_inv).mul(a01),
    );
    T::axiom_mul_congruence_left(d.mul(d_inv), T::one(), a01);
    ring_lemmas::lemma_mul_one_left::<T>(a01);
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a01.neg()).neg()),
        d.mul(d_inv).mul(a01),
        T::one().mul(a01),
    );
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a01.neg()).neg()),
        T::one().mul(a01),
        a01,
    );

    // inverse(inv).row1.x = recip_det_inv * adjugate(inv).row1.x
    // adjugate(inv).row1.x = inv.row1.x.neg() = (d_inv * a10.neg()).neg()
    // Same pattern as row0.y: (d_inv * (-a10)).neg() ≡ d_inv * a10
    ring_lemmas::lemma_mul_neg_right::<T>(d_inv, a10);
    additive_group_lemmas::lemma_neg_congruence::<T>(d_inv.mul(a10.neg()), d_inv.mul(a10).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(d_inv.mul(a10));
    T::axiom_eqv_transitive(
        d_inv.mul(a10.neg()).neg(),
        d_inv.mul(a10).neg().neg(),
        d_inv.mul(a10),
    );

    // recip_det_inv * (d_inv * a10) ≡ a10
    ring_lemmas::lemma_mul_congruence_right::<T>(recip_det_inv, d_inv.mul(a10.neg()).neg(), d_inv.mul(a10));
    T::axiom_mul_congruence_left(recip_det_inv, d, d_inv.mul(a10));
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a10.neg()).neg()),
        recip_det_inv.mul(d_inv.mul(a10)),
        d.mul(d_inv.mul(a10)),
    );
    T::axiom_mul_associative(d, d_inv, a10);
    T::axiom_eqv_symmetric(d.mul(d_inv).mul(a10), d.mul(d_inv.mul(a10)));
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a10.neg()).neg()),
        d.mul(d_inv.mul(a10)),
        d.mul(d_inv).mul(a10),
    );
    T::axiom_mul_congruence_left(d.mul(d_inv), T::one(), a10);
    ring_lemmas::lemma_mul_one_left::<T>(a10);
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a10.neg()).neg()),
        d.mul(d_inv).mul(a10),
        T::one().mul(a10),
    );
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a10.neg()).neg()),
        T::one().mul(a10),
        a10,
    );

    // inverse(inv).row1.y = recip_det_inv * adjugate(inv).row1.y
    // adjugate(inv).row1.y = inv.row0.x = d_inv * a11
    // recip_det_inv * (d_inv * a11) ≡ a11
    T::axiom_mul_congruence_left(recip_det_inv, d, d_inv.mul(a11));
    T::axiom_mul_associative(d, d_inv, a11);
    T::axiom_eqv_symmetric(d.mul(d_inv).mul(a11), d.mul(d_inv.mul(a11)));
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a11)),
        d.mul(d_inv.mul(a11)),
        d.mul(d_inv).mul(a11),
    );
    T::axiom_mul_congruence_left(d.mul(d_inv), T::one(), a11);
    ring_lemmas::lemma_mul_one_left::<T>(a11);
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a11)),
        d.mul(d_inv).mul(a11),
        T::one().mul(a11),
    );
    T::axiom_eqv_transitive(
        recip_det_inv.mul(d_inv.mul(a11)),
        T::one().mul(a11),
        a11,
    );
}

} // verus!
