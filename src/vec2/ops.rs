use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_commutative_monoid_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::inequalities;
use super::Vec2;

verus! {

// ---------------------------------------------------------------------------
// Spec functions
// ---------------------------------------------------------------------------

pub open spec fn scale<T: Ring>(s: T, v: Vec2<T>) -> Vec2<T> {
    Vec2 { x: s.mul(v.x), y: s.mul(v.y) }
}

pub open spec fn dot<T: Ring>(a: Vec2<T>, b: Vec2<T>) -> T {
    a.x.mul(b.x).add(a.y.mul(b.y))
}

pub open spec fn norm_sq<T: Ring>(v: Vec2<T>) -> T {
    dot(v, v)
}

// ---------------------------------------------------------------------------
// Scale lemmas
// ---------------------------------------------------------------------------

/// scale(s, a + b) ≡ scale(s, a) + scale(s, b)
pub proof fn lemma_scale_distributes_over_add<T: Ring>(s: T, a: Vec2<T>, b: Vec2<T>)
    ensures
        scale(s, a.add(b)).eqv(scale(s, a).add(scale(s, b))),
{
    T::axiom_mul_distributes_left(s, a.x, b.x);
    T::axiom_mul_distributes_left(s, a.y, b.y);
}

/// scale(s + t, a) ≡ scale(s, a) + scale(t, a)
pub proof fn lemma_scale_add_distributes<T: Ring>(s: T, t: T, a: Vec2<T>)
    ensures
        scale(s.add(t), a).eqv(scale(s, a).add(scale(t, a))),
{
    ring_lemmas::lemma_mul_distributes_right::<T>(s, t, a.x);
    ring_lemmas::lemma_mul_distributes_right::<T>(s, t, a.y);
}

/// scale(1, a) ≡ a
pub proof fn lemma_scale_identity<T: Ring>(a: Vec2<T>)
    ensures
        scale(T::one(), a).eqv(a),
{
    ring_lemmas::lemma_mul_one_left::<T>(a.x);
    ring_lemmas::lemma_mul_one_left::<T>(a.y);
}

/// scale(0, a) ≡ zero
pub proof fn lemma_scale_zero_scalar<T: Ring>(a: Vec2<T>)
    ensures
        scale(T::zero(), a).eqv(Vec2 { x: T::zero(), y: T::zero() }),
{
    ring_lemmas::lemma_mul_zero_left::<T>(a.x);
    ring_lemmas::lemma_mul_zero_left::<T>(a.y);
}

/// scale(s, zero) ≡ zero
pub proof fn lemma_scale_zero_vec<T: Ring>(s: T)
    ensures
        scale(s, Vec2 { x: T::zero(), y: T::zero() })
            .eqv(Vec2 { x: T::zero(), y: T::zero() }),
{
    T::axiom_mul_zero_right(s);
}

/// a ≡ b implies scale(s, a) ≡ scale(s, b)
pub proof fn lemma_scale_congruence<T: Ring>(s: T, a: Vec2<T>, b: Vec2<T>)
    requires
        a.eqv(b),
    ensures
        scale(s, a).eqv(scale(s, b)),
{
    ring_lemmas::lemma_mul_congruence_right::<T>(s, a.x, b.x);
    ring_lemmas::lemma_mul_congruence_right::<T>(s, a.y, b.y);
}

/// scale(s, scale(t, a)) ≡ scale(s * t, a)
pub proof fn lemma_scale_associative<T: Ring>(s: T, t: T, a: Vec2<T>)
    ensures
        scale(s, scale(t, a)).eqv(scale(s.mul(t), a)),
{
    // (s*t)*a.x ≡ s*(t*a.x), need symmetric
    T::axiom_mul_associative(s, t, a.x);
    T::axiom_eqv_symmetric(s.mul(t).mul(a.x), s.mul(t.mul(a.x)));
    T::axiom_mul_associative(s, t, a.y);
    T::axiom_eqv_symmetric(s.mul(t).mul(a.y), s.mul(t.mul(a.y)));
}

/// scale(-s, a) ≡ -scale(s, a)
pub proof fn lemma_scale_neg_scalar<T: Ring>(s: T, a: Vec2<T>)
    ensures
        scale(s.neg(), a).eqv(scale(s, a).neg()),
{
    ring_lemmas::lemma_mul_neg_left::<T>(s, a.x);
    ring_lemmas::lemma_mul_neg_left::<T>(s, a.y);
}

/// scale(s, -a) ≡ -scale(s, a)
pub proof fn lemma_scale_neg_vec<T: Ring>(s: T, a: Vec2<T>)
    ensures
        scale(s, a.neg()).eqv(scale(s, a).neg()),
{
    ring_lemmas::lemma_mul_neg_right::<T>(s, a.x);
    ring_lemmas::lemma_mul_neg_right::<T>(s, a.y);
}

/// scale(s, a - b) ≡ scale(s, a) - scale(s, b)
pub proof fn lemma_scale_sub_distributes<T: Ring>(s: T, a: Vec2<T>, b: Vec2<T>)
    ensures
        scale(s, a.sub(b)).eqv(scale(s, a).sub(scale(s, b))),
{
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.x, b.x);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.y, b.y);
}

// ---------------------------------------------------------------------------
// Dot lemmas
// ---------------------------------------------------------------------------

/// dot(a, b) ≡ dot(b, a)
pub proof fn lemma_dot_commutative<T: Ring>(a: Vec2<T>, b: Vec2<T>)
    ensures
        dot(a, b).eqv(dot(b, a)),
{
    T::axiom_mul_commutative(a.x, b.x);
    T::axiom_mul_commutative(a.y, b.y);
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(b.x), b.x.mul(a.x),
        a.y.mul(b.y), b.y.mul(a.y),
    );
}

/// dot(a, zero) ≡ 0
pub proof fn lemma_dot_zero_right<T: Ring>(a: Vec2<T>)
    ensures
        dot(a, Vec2 { x: T::zero(), y: T::zero() }).eqv(T::zero()),
{
    T::axiom_mul_zero_right(a.x);
    T::axiom_mul_zero_right(a.y);
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(T::zero()), T::zero(),
        a.y.mul(T::zero()), T::zero(),
    );
    T::axiom_add_zero_right(T::zero());
    T::axiom_eqv_transitive(
        a.x.mul(T::zero()).add(a.y.mul(T::zero())),
        T::zero().add(T::zero()),
        T::zero(),
    );
}

/// dot(zero, a) ≡ 0
pub proof fn lemma_dot_zero_left<T: Ring>(a: Vec2<T>)
    ensures
        dot(Vec2 { x: T::zero(), y: T::zero() }, a).eqv(T::zero()),
{
    ring_lemmas::lemma_mul_zero_left::<T>(a.x);
    ring_lemmas::lemma_mul_zero_left::<T>(a.y);
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(a.x), T::zero(),
        T::zero().mul(a.y), T::zero(),
    );
    T::axiom_add_zero_right(T::zero());
    T::axiom_eqv_transitive(
        T::zero().mul(a.x).add(T::zero().mul(a.y)),
        T::zero().add(T::zero()),
        T::zero(),
    );
}

/// dot(a, b + c) ≡ dot(a, b) + dot(a, c)
pub proof fn lemma_dot_distributes_right<T: Ring>(a: Vec2<T>, b: Vec2<T>, c: Vec2<T>)
    ensures
        dot(a, b.add(c)).eqv(dot(a, b).add(dot(a, c))),
{
    // Distribute each component
    T::axiom_mul_distributes_left(a.x, b.x, c.x);
    T::axiom_mul_distributes_left(a.y, b.y, c.y);
    // Propagate: LHS ≡ (ax*bx + ax*cx) + (ay*by + ay*cy)
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(b.x.add(c.x)), a.x.mul(b.x).add(a.x.mul(c.x)),
        a.y.mul(b.y.add(c.y)), a.y.mul(b.y).add(a.y.mul(c.y)),
    );
    // Rearrange: ≡ (ax*bx + ay*by) + (ax*cx + ay*cy) = dot(a,b) + dot(a,c)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.x.mul(b.x), a.x.mul(c.x), a.y.mul(b.y), a.y.mul(c.y),
    );
    // Chain
    T::axiom_eqv_transitive(
        dot(a, b.add(c)),
        a.x.mul(b.x).add(a.x.mul(c.x)).add(a.y.mul(b.y).add(a.y.mul(c.y))),
        dot(a, b).add(dot(a, c)),
    );
}

/// dot(a + b, c) ≡ dot(a, c) + dot(b, c)
pub proof fn lemma_dot_distributes_left<T: Ring>(a: Vec2<T>, b: Vec2<T>, c: Vec2<T>)
    ensures
        dot(a.add(b), c).eqv(dot(a, c).add(dot(b, c))),
{
    // Distribute each component
    ring_lemmas::lemma_mul_distributes_right::<T>(a.x, b.x, c.x);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.y, b.y, c.y);
    // Propagate: LHS ≡ (ax*cx + bx*cx) + (ay*cy + by*cy)
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.add(b.x).mul(c.x), a.x.mul(c.x).add(b.x.mul(c.x)),
        a.y.add(b.y).mul(c.y), a.y.mul(c.y).add(b.y.mul(c.y)),
    );
    // Rearrange: ≡ (ax*cx + ay*cy) + (bx*cx + by*cy) = dot(a,c) + dot(b,c)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.x.mul(c.x), b.x.mul(c.x), a.y.mul(c.y), b.y.mul(c.y),
    );
    // Chain
    T::axiom_eqv_transitive(
        dot(a.add(b), c),
        a.x.mul(c.x).add(b.x.mul(c.x)).add(a.y.mul(c.y).add(b.y.mul(c.y))),
        dot(a, c).add(dot(b, c)),
    );
}

/// dot(scale(s, a), b) ≡ s * dot(a, b)
pub proof fn lemma_dot_scale_left<T: Ring>(s: T, a: Vec2<T>, b: Vec2<T>)
    ensures
        dot(scale(s, a), b).eqv(s.mul(dot(a, b))),
{
    // (s*ax)*bx ≡ s*(ax*bx), (s*ay)*by ≡ s*(ay*by)
    T::axiom_mul_associative(s, a.x, b.x);
    T::axiom_mul_associative(s, a.y, b.y);
    // LHS ≡ s*(ax*bx) + s*(ay*by)
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        s.mul(a.x).mul(b.x), s.mul(a.x.mul(b.x)),
        s.mul(a.y).mul(b.y), s.mul(a.y.mul(b.y)),
    );
    // s*(ax*bx + ay*by) ≡ s*(ax*bx) + s*(ay*by)
    T::axiom_mul_distributes_left(s, a.x.mul(b.x), a.y.mul(b.y));
    // Reverse: s*(ax*bx) + s*(ay*by) ≡ s*(ax*bx + ay*by)
    T::axiom_eqv_symmetric(
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y))),
        s.mul(a.x.mul(b.x)).add(s.mul(a.y.mul(b.y))),
    );
    // Chain
    T::axiom_eqv_transitive(
        dot(scale(s, a), b),
        s.mul(a.x.mul(b.x)).add(s.mul(a.y.mul(b.y))),
        s.mul(dot(a, b)),
    );
}

/// dot(a, scale(s, b)) ≡ s * dot(a, b)
pub proof fn lemma_dot_scale_right<T: Ring>(s: T, a: Vec2<T>, b: Vec2<T>)
    ensures
        dot(a, scale(s, b)).eqv(s.mul(dot(a, b))),
{
    // dot(a, scale(s,b)) ≡ dot(scale(s,b), a)
    lemma_dot_commutative(a, scale(s, b));
    // dot(scale(s,b), a) ≡ s*dot(b, a)
    lemma_dot_scale_left(s, b, a);
    T::axiom_eqv_transitive(
        dot(a, scale(s, b)),
        dot(scale(s, b), a),
        s.mul(dot(b, a)),
    );
    // dot(b, a) ≡ dot(a, b)
    lemma_dot_commutative(b, a);
    ring_lemmas::lemma_mul_congruence_right::<T>(s, dot(b, a), dot(a, b));
    T::axiom_eqv_transitive(
        dot(a, scale(s, b)),
        s.mul(dot(b, a)),
        s.mul(dot(a, b)),
    );
}

// ---------------------------------------------------------------------------
// Dot congruence and neg
// ---------------------------------------------------------------------------

/// a1 ≡ a2, b1 ≡ b2 implies dot(a1, b1) ≡ dot(a2, b2)
pub proof fn lemma_dot_congruence<T: Ring>(a1: Vec2<T>, a2: Vec2<T>, b1: Vec2<T>, b2: Vec2<T>)
    requires
        a1.eqv(a2),
        b1.eqv(b2),
    ensures
        dot(a1, b1).eqv(dot(a2, b2)),
{
    ring_lemmas::lemma_mul_congruence::<T>(a1.x, a2.x, b1.x, b2.x);
    ring_lemmas::lemma_mul_congruence::<T>(a1.y, a2.y, b1.y, b2.y);
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a1.x.mul(b1.x), a2.x.mul(b2.x),
        a1.y.mul(b1.y), a2.y.mul(b2.y),
    );
}

/// dot(a, -b) ≡ -dot(a, b)
pub proof fn lemma_dot_neg_right<T: Ring>(a: Vec2<T>, b: Vec2<T>)
    ensures
        dot(a, b.neg()).eqv(dot(a, b).neg()),
{
    // a.x*(-b.x) ≡ -(a.x*b.x)
    ring_lemmas::lemma_mul_neg_right::<T>(a.x, b.x);
    // a.y*(-b.y) ≡ -(a.y*b.y)
    ring_lemmas::lemma_mul_neg_right::<T>(a.y, b.y);
    // LHS ≡ -(a.x*b.x) + -(a.y*b.y)
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(b.x.neg()), a.x.mul(b.x).neg(),
        a.y.mul(b.y.neg()), a.y.mul(b.y).neg(),
    );
    // -(a.x*b.x) + -(a.y*b.y) ≡ -(a.x*b.x + a.y*b.y)
    additive_group_lemmas::lemma_neg_add::<T>(a.x.mul(b.x), a.y.mul(b.y));
    T::axiom_eqv_symmetric(
        a.x.mul(b.x).add(a.y.mul(b.y)).neg(),
        a.x.mul(b.x).neg().add(a.y.mul(b.y).neg()),
    );
    // Chain
    T::axiom_eqv_transitive(
        dot(a, b.neg()),
        a.x.mul(b.x).neg().add(a.y.mul(b.y).neg()),
        dot(a, b).neg(),
    );
}

// ---------------------------------------------------------------------------
// Norm-squared lemmas
// ---------------------------------------------------------------------------

/// a ≡ b implies norm_sq(a) ≡ norm_sq(b)
pub proof fn lemma_norm_sq_congruence<T: Ring>(a: Vec2<T>, b: Vec2<T>)
    requires
        a.eqv(b),
    ensures
        norm_sq(a).eqv(norm_sq(b)),
{
    lemma_dot_congruence(a, b, a, b);
}

/// norm_sq(scale(s, v)) ≡ s*s * norm_sq(v)
pub proof fn lemma_norm_sq_scale<T: Ring>(s: T, v: Vec2<T>)
    ensures
        norm_sq(scale(s, v)).eqv(s.mul(s).mul(norm_sq(v))),
{
    // norm_sq(scale(s,v)) = dot(scale(s,v), scale(s,v))
    // ≡ s * dot(v, scale(s,v))  [dot_scale_left]
    lemma_dot_scale_left(s, v, scale(s, v));
    // s * dot(v, scale(s,v)) ≡ s * (s * dot(v,v))  [dot_scale_right inside]
    lemma_dot_scale_right(s, v, v);
    ring_lemmas::lemma_mul_congruence_right::<T>(s, dot(v, scale(s, v)), s.mul(dot(v, v)));
    T::axiom_eqv_transitive(
        norm_sq(scale(s, v)),
        s.mul(dot(v, scale(s, v))),
        s.mul(s.mul(dot(v, v))),
    );
    // s * (s * dot(v,v)) ≡ (s*s) * dot(v,v)  [assoc reversed]
    T::axiom_mul_associative(s, s, dot(v, v));
    T::axiom_eqv_symmetric(s.mul(s).mul(dot(v, v)), s.mul(s.mul(dot(v, v))));
    T::axiom_eqv_transitive(
        norm_sq(scale(s, v)),
        s.mul(s.mul(dot(v, v))),
        s.mul(s).mul(norm_sq(v)),
    );
}

/// 0 ≤ norm_sq(v)
pub proof fn lemma_norm_sq_nonneg<T: OrderedRing>(v: Vec2<T>)
    ensures
        T::zero().le(norm_sq(v)),
{
    inequalities::lemma_sum_squares_nonneg_2d::<T>(v.x, v.y);
}

/// norm_sq(v) ≡ 0 implies v ≡ zero (for OrderedField)
pub proof fn lemma_norm_sq_zero_implies_zero<T: OrderedField>(v: Vec2<T>)
    requires
        norm_sq(v).eqv(T::zero()),
    ensures
        v.eqv(Vec2 { x: T::zero(), y: T::zero() }),
{
    inequalities::lemma_sum_squares_zero_2d::<T>(v.x, v.y);
}

/// v ≡ zero implies norm_sq(v) ≡ 0
pub proof fn lemma_norm_sq_zero_of_zero<T: Ring>(v: Vec2<T>)
    requires
        v.eqv(Vec2 { x: T::zero(), y: T::zero() }),
    ensures
        norm_sq(v).eqv(T::zero()),
{
    let z = Vec2 { x: T::zero(), y: T::zero() };
    lemma_dot_congruence(v, z, v, z);
    lemma_dot_zero_right(z);
    T::axiom_eqv_transitive(norm_sq(v), dot(z, z), T::zero());
}

// ---------------------------------------------------------------------------
// Cauchy-Schwarz inequality
// ---------------------------------------------------------------------------

/// dot(a,b)² <= norm_sq(a) * norm_sq(b)
pub proof fn lemma_cauchy_schwarz<T: OrderedRing>(a: Vec2<T>, b: Vec2<T>)
    ensures
        dot(a, b).mul(dot(a, b)).le(norm_sq(a).mul(norm_sq(b))),
{
    inequalities::lemma_cauchy_schwarz_2d::<T>(a.x, a.y, b.x, b.y);
}

} // verus!
