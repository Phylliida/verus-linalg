use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_commutative_monoid_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::lemmas::field_lemmas;
use verus_algebra::inequalities;
use verus_algebra::min_max;
use verus_algebra::convex::two;
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

pub open spec fn lerp<T: Ring>(a: Vec2<T>, b: Vec2<T>, t: T) -> Vec2<T> {
    scale(T::one().sub(t), a).add(scale(t, b))
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
// Lerp lemmas
// ---------------------------------------------------------------------------

/// lerp(a, b, 0) ≡ a
pub proof fn lemma_lerp_zero<T: Ring>(a: Vec2<T>, b: Vec2<T>)
    ensures
        lerp(a, b, T::zero()).eqv(a),
{
    // 1 - 0 ≡ 1
    T::axiom_sub_is_add_neg(T::one(), T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        T::one(), T::zero().neg(), T::zero(),
    );
    T::axiom_add_zero_right(T::one());
    T::axiom_eqv_transitive(
        T::one().sub(T::zero()), T::one().add(T::zero().neg()), T::one().add(T::zero()),
    );
    T::axiom_eqv_transitive(
        T::one().sub(T::zero()), T::one().add(T::zero()), T::one(),
    );

    // (1-0)*a.x ≡ a.x, (1-0)*a.y ≡ a.y
    T::axiom_mul_congruence_left(T::one().sub(T::zero()), T::one(), a.x);
    T::axiom_mul_congruence_left(T::one().sub(T::zero()), T::one(), a.y);
    ring_lemmas::lemma_mul_one_left::<T>(a.x);
    ring_lemmas::lemma_mul_one_left::<T>(a.y);
    T::axiom_eqv_transitive(T::one().sub(T::zero()).mul(a.x), T::one().mul(a.x), a.x);
    T::axiom_eqv_transitive(T::one().sub(T::zero()).mul(a.y), T::one().mul(a.y), a.y);

    // 0*b.x ≡ 0, 0*b.y ≡ 0
    ring_lemmas::lemma_mul_zero_left::<T>(b.x);
    ring_lemmas::lemma_mul_zero_left::<T>(b.y);

    // (1-0)*a.x + 0*b.x ≡ a.x + 0
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().sub(T::zero()).mul(a.x), a.x,
        T::zero().mul(b.x), T::zero(),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().sub(T::zero()).mul(a.y), a.y,
        T::zero().mul(b.y), T::zero(),
    );

    // a.x + 0 ≡ a.x, chain to conclude
    T::axiom_add_zero_right(a.x);
    T::axiom_add_zero_right(a.y);
    T::axiom_eqv_transitive(
        T::one().sub(T::zero()).mul(a.x).add(T::zero().mul(b.x)),
        a.x.add(T::zero()), a.x,
    );
    T::axiom_eqv_transitive(
        T::one().sub(T::zero()).mul(a.y).add(T::zero().mul(b.y)),
        a.y.add(T::zero()), a.y,
    );
}

/// lerp(a, b, 1) ≡ b
pub proof fn lemma_lerp_one<T: Ring>(a: Vec2<T>, b: Vec2<T>)
    ensures
        lerp(a, b, T::one()).eqv(b),
{
    // 1 - 1 ≡ 0
    additive_group_lemmas::lemma_sub_self::<T>(T::one());

    // (1-1)*a.x ≡ 0
    T::axiom_mul_congruence_left(T::one().sub(T::one()), T::zero(), a.x);
    T::axiom_mul_congruence_left(T::one().sub(T::one()), T::zero(), a.y);
    ring_lemmas::lemma_mul_zero_left::<T>(a.x);
    ring_lemmas::lemma_mul_zero_left::<T>(a.y);
    T::axiom_eqv_transitive(T::one().sub(T::one()).mul(a.x), T::zero().mul(a.x), T::zero());
    T::axiom_eqv_transitive(T::one().sub(T::one()).mul(a.y), T::zero().mul(a.y), T::zero());

    // 1*b.x ≡ b.x
    ring_lemmas::lemma_mul_one_left::<T>(b.x);
    ring_lemmas::lemma_mul_one_left::<T>(b.y);

    // (1-1)*a.x + 1*b.x ≡ 0 + b.x
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().sub(T::one()).mul(a.x), T::zero(),
        T::one().mul(b.x), b.x,
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().sub(T::one()).mul(a.y), T::zero(),
        T::one().mul(b.y), b.y,
    );

    // 0 + b.x ≡ b.x, chain to conclude
    additive_group_lemmas::lemma_add_zero_left::<T>(b.x);
    additive_group_lemmas::lemma_add_zero_left::<T>(b.y);
    T::axiom_eqv_transitive(
        T::one().sub(T::one()).mul(a.x).add(T::one().mul(b.x)),
        T::zero().add(b.x), b.x,
    );
    T::axiom_eqv_transitive(
        T::one().sub(T::one()).mul(a.y).add(T::one().mul(b.y)),
        T::zero().add(b.y), b.y,
    );
}

/// lerp(a, a, t) ≡ a
pub proof fn lemma_lerp_self<T: Ring>(a: Vec2<T>, t: T)
    ensures
        lerp(a, a, t).eqv(a),
{
    // scale(1-t, a) + scale(t, a) ≡ scale((1-t)+t, a) [reverse of scale_add_distributes]
    lemma_scale_add_distributes(T::one().sub(t), t, a);
    Vec2::<T>::axiom_eqv_symmetric(
        scale(T::one().sub(t).add(t), a),
        scale(T::one().sub(t), a).add(scale(t, a)),
    );

    // (1-t)+t ≡ 1
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(T::one(), t);

    // scale((1-t)+t, a) ≡ scale(1, a) ≡ a
    T::axiom_mul_congruence_left(T::one().sub(t).add(t), T::one(), a.x);
    T::axiom_mul_congruence_left(T::one().sub(t).add(t), T::one(), a.y);
    ring_lemmas::lemma_mul_one_left::<T>(a.x);
    ring_lemmas::lemma_mul_one_left::<T>(a.y);
    T::axiom_eqv_transitive(T::one().sub(t).add(t).mul(a.x), T::one().mul(a.x), a.x);
    T::axiom_eqv_transitive(T::one().sub(t).add(t).mul(a.y), T::one().mul(a.y), a.y);

    // Chain: lerp(a, a, t) ≡ scale((1-t)+t, a) ≡ a
    Vec2::<T>::axiom_eqv_transitive(
        lerp(a, a, t),
        scale(T::one().sub(t).add(t), a),
        a,
    );
}

// ---------------------------------------------------------------------------
// Inner product identities
// ---------------------------------------------------------------------------

/// norm_sq(a+b) ≡ norm_sq(a) + 2·dot(a,b) + norm_sq(b)
proof fn lemma_norm_sq_add_expand<T: Ring>(a: Vec2<T>, b: Vec2<T>)
    ensures
        norm_sq(a.add(b)).eqv(
            norm_sq(a).add(two::<T>().mul(dot(a, b))).add(norm_sq(b))
        ),
{
    let na = norm_sq(a);
    let nb = norm_sq(b);
    let d = dot(a, b);

    // dot(a+b, a+b) ≡ dot(a, a+b) + dot(b, a+b)
    lemma_dot_distributes_left(a, b, a.add(b));
    // dot(a, a+b) ≡ norm_sq(a) + dot(a,b)
    lemma_dot_distributes_right(a, a, b);
    // dot(b, a+b) ≡ dot(b,a) + norm_sq(b)
    lemma_dot_distributes_right(b, a, b);

    // dot(b,a) ≡ dot(a,b)
    lemma_dot_commutative(b, a);
    T::axiom_eqv_reflexive(nb);
    additive_group_lemmas::lemma_add_congruence::<T>(
        dot(b, a), d, dot(b, b), nb,
    );
    // dot(b, a+b) ≡ dot(a,b) + norm_sq(b)
    T::axiom_eqv_transitive(
        dot(b, a.add(b)), dot(b, a).add(dot(b, b)), d.add(nb),
    );

    // Combine: norm_sq(a+b) ≡ (na + d) + (d + nb)
    additive_group_lemmas::lemma_add_congruence::<T>(
        dot(a, a.add(b)), na.add(d),
        dot(b, a.add(b)), d.add(nb),
    );
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)),
        dot(a, a.add(b)).add(dot(b, a.add(b))),
        na.add(d).add(d.add(nb)),
    );

    // Reassociate: (na+d) + (d+nb) ≡ ((na+d)+d) + nb
    T::axiom_add_associative(na.add(d), d, nb);
    T::axiom_eqv_symmetric(na.add(d).add(d).add(nb), na.add(d).add(d.add(nb)));
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)),
        na.add(d).add(d.add(nb)),
        na.add(d).add(d).add(nb),
    );

    // Inner: (na+d)+d ≡ na+(d+d)
    T::axiom_add_associative(na, d, d);
    T::axiom_eqv_reflexive(nb);
    additive_group_lemmas::lemma_add_congruence::<T>(
        na.add(d).add(d), na.add(d.add(d)), nb, nb,
    );
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)),
        na.add(d).add(d).add(nb),
        na.add(d.add(d)).add(nb),
    );

    // mul_two: d+d ≡ two*d
    ring_lemmas::lemma_mul_two::<T>(d);
    additive_group_lemmas::lemma_add_congruence_right::<T>(na, d.add(d), two::<T>().mul(d));
    T::axiom_eqv_reflexive(nb);
    additive_group_lemmas::lemma_add_congruence::<T>(
        na.add(d.add(d)), na.add(two::<T>().mul(d)), nb, nb,
    );
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)),
        na.add(d.add(d)).add(nb),
        na.add(two::<T>().mul(d)).add(nb),
    );
}

/// Pythagorean theorem: if dot(a,b) ≡ 0, then norm_sq(a+b) ≡ norm_sq(a) + norm_sq(b)
pub proof fn lemma_pythagorean<T: Ring>(a: Vec2<T>, b: Vec2<T>)
    requires
        dot(a, b).eqv(T::zero()),
    ensures
        norm_sq(a.add(b)).eqv(norm_sq(a).add(norm_sq(b))),
{
    let na = norm_sq(a);
    let nb = norm_sq(b);
    let d = dot(a, b);

    // norm_sq(a+b) ≡ na + two*d + nb
    lemma_norm_sq_add_expand(a, b);

    // two*d ≡ two*0
    ring_lemmas::lemma_mul_congruence_right::<T>(two::<T>(), d, T::zero());
    // two*0 ≡ 0
    T::axiom_mul_zero_right(two::<T>());
    T::axiom_eqv_transitive(two::<T>().mul(d), two::<T>().mul(T::zero()), T::zero());

    // na + two*d ≡ na + 0
    additive_group_lemmas::lemma_add_congruence_right::<T>(na, two::<T>().mul(d), T::zero());
    // na + 0 ≡ na
    T::axiom_add_zero_right(na);
    T::axiom_eqv_transitive(na.add(two::<T>().mul(d)), na.add(T::zero()), na);

    // (na + two*d) + nb ≡ na + nb
    T::axiom_eqv_reflexive(nb);
    additive_group_lemmas::lemma_add_congruence::<T>(
        na.add(two::<T>().mul(d)), na, nb, nb,
    );

    // Chain: norm_sq(a+b) ≡ (na + two*d) + nb ≡ na + nb
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)),
        na.add(two::<T>().mul(d)).add(nb),
        na.add(nb),
    );
}

/// norm_sq(a-b) ≡ norm_sq(a) - 2·dot(a,b) + norm_sq(b)
proof fn lemma_norm_sq_sub_expand<T: Ring>(a: Vec2<T>, b: Vec2<T>)
    ensures
        norm_sq(a.sub(b)).eqv(
            norm_sq(a).sub(two::<T>().mul(dot(a, b))).add(norm_sq(b))
        ),
{
    let na = norm_sq(a);
    let nb = norm_sq(b);
    let d = dot(a, b);
    let t = two::<T>();
    let neg_b = b.neg();

    // norm_sq(a-b) ≡ norm_sq(a+(-b))
    Vec2::<T>::axiom_sub_is_add_neg(a, b);
    lemma_norm_sq_congruence(a.sub(b), a.add(neg_b));

    // ≡ na + two*dot(a,-b) + norm_sq(-b)
    lemma_norm_sq_add_expand(a, neg_b);
    T::axiom_eqv_transitive(
        norm_sq(a.sub(b)), norm_sq(a.add(neg_b)),
        na.add(t.mul(dot(a, neg_b))).add(norm_sq(neg_b)),
    );

    // two*dot(a,-b) ≡ -(two*d)
    lemma_dot_neg_right(a, b);
    ring_lemmas::lemma_mul_congruence_right::<T>(t, dot(a, neg_b), d.neg());
    ring_lemmas::lemma_mul_neg_right::<T>(t, d);
    T::axiom_eqv_transitive(t.mul(dot(a, neg_b)), t.mul(d.neg()), t.mul(d).neg());

    // norm_sq(-b) ≡ nb via double negation
    lemma_dot_neg_right(neg_b, b);   // dot(-b, -b) ≡ dot(-b, b).neg()
    lemma_dot_commutative(neg_b, b);  // dot(-b, b) ≡ dot(b, -b)
    lemma_dot_neg_right(b, b);        // dot(b, -b) ≡ -nb
    T::axiom_eqv_transitive(dot(neg_b, b), dot(b, neg_b), nb.neg());
    additive_group_lemmas::lemma_neg_congruence::<T>(dot(neg_b, b), nb.neg());
    T::axiom_eqv_transitive(norm_sq(neg_b), dot(neg_b, b).neg(), nb.neg().neg());
    additive_group_lemmas::lemma_neg_involution::<T>(nb);
    T::axiom_eqv_transitive(norm_sq(neg_b), nb.neg().neg(), nb);

    // na + two*dot(a,-b) ≡ na + (-(t*d)) ≡ na - t*d
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        na, t.mul(dot(a, neg_b)), t.mul(d).neg(),
    );
    T::axiom_sub_is_add_neg(na, t.mul(d));
    T::axiom_eqv_symmetric(na.sub(t.mul(d)), na.add(t.mul(d).neg()));
    T::axiom_eqv_transitive(
        na.add(t.mul(dot(a, neg_b))), na.add(t.mul(d).neg()), na.sub(t.mul(d)),
    );

    // Combine: ≡ (na - t*d) + nb
    additive_group_lemmas::lemma_add_congruence::<T>(
        na.add(t.mul(dot(a, neg_b))), na.sub(t.mul(d)),
        norm_sq(neg_b), nb,
    );
    T::axiom_eqv_transitive(
        norm_sq(a.sub(b)),
        na.add(t.mul(dot(a, neg_b))).add(norm_sq(neg_b)),
        na.sub(t.mul(d)).add(nb),
    );
}

/// Parallelogram law: norm_sq(a+b) + norm_sq(a-b) ≡ 2·(norm_sq(a) + norm_sq(b))
pub proof fn lemma_parallelogram<T: Ring>(a: Vec2<T>, b: Vec2<T>)
    ensures
        norm_sq(a.add(b)).add(norm_sq(a.sub(b))).eqv(
            two::<T>().mul(norm_sq(a).add(norm_sq(b)))
        ),
{
    let na = norm_sq(a);
    let nb = norm_sq(b);
    let t = two::<T>();
    let td = t.mul(dot(a, b));

    lemma_norm_sq_add_expand(a, b);
    lemma_norm_sq_sub_expand(a, b);

    // Sum ≡ ((na+td)+nb) + ((na-td)+nb)
    additive_group_lemmas::lemma_add_congruence::<T>(
        norm_sq(a.add(b)), na.add(td).add(nb),
        norm_sq(a.sub(b)), na.sub(td).add(nb),
    );

    // Rearrange: ≡ ((na+td)+(na-td)) + (nb+nb)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        na.add(td), nb, na.sub(td), nb,
    );
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)).add(norm_sq(a.sub(b))),
        na.add(td).add(nb).add(na.sub(td).add(nb)),
        na.add(td).add(na.sub(td)).add(nb.add(nb)),
    );

    // (na+td) + (na-td) ≡ na + na
    T::axiom_sub_is_add_neg(na, td);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        na.add(td), na.sub(td), na.add(td.neg()),
    );
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(na, td, na, td.neg());
    T::axiom_eqv_transitive(
        na.add(td).add(na.sub(td)),
        na.add(td).add(na.add(td.neg())),
        na.add(na).add(td.add(td.neg())),
    );
    T::axiom_add_inverse_right(td);
    T::axiom_eqv_reflexive(na.add(na));
    additive_group_lemmas::lemma_add_congruence::<T>(
        na.add(na), na.add(na), td.add(td.neg()), T::zero(),
    );
    T::axiom_add_zero_right(na.add(na));
    T::axiom_eqv_transitive(
        na.add(td).add(na.sub(td)),
        na.add(na).add(td.add(td.neg())),
        na.add(na).add(T::zero()),
    );
    T::axiom_eqv_transitive(
        na.add(td).add(na.sub(td)), na.add(na).add(T::zero()), na.add(na),
    );

    // na+na ≡ t*na, nb+nb ≡ t*nb
    ring_lemmas::lemma_mul_two::<T>(na);
    ring_lemmas::lemma_mul_two::<T>(nb);

    // ((na+td)+(na-td)) + (nb+nb) ≡ na+na + nb+nb
    T::axiom_eqv_reflexive(nb.add(nb));
    additive_group_lemmas::lemma_add_congruence::<T>(
        na.add(td).add(na.sub(td)), na.add(na), nb.add(nb), nb.add(nb),
    );
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)).add(norm_sq(a.sub(b))),
        na.add(td).add(na.sub(td)).add(nb.add(nb)),
        na.add(na).add(nb.add(nb)),
    );

    // na+na + nb+nb ≡ t*na + t*nb
    additive_group_lemmas::lemma_add_congruence::<T>(
        na.add(na), t.mul(na), nb.add(nb), t.mul(nb),
    );
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)).add(norm_sq(a.sub(b))),
        na.add(na).add(nb.add(nb)),
        t.mul(na).add(t.mul(nb)),
    );

    // t*na + t*nb ≡ t*(na+nb)
    T::axiom_mul_distributes_left(t, na, nb);
    T::axiom_eqv_symmetric(t.mul(na.add(nb)), t.mul(na).add(t.mul(nb)));
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)).add(norm_sq(a.sub(b))),
        t.mul(na).add(t.mul(nb)),
        t.mul(na.add(nb)),
    );
}

/// Polarization identity: 4·dot(a,b) ≡ norm_sq(a+b) - norm_sq(a-b)
pub proof fn lemma_polarization<T: Ring>(a: Vec2<T>, b: Vec2<T>)
    ensures
        two::<T>().mul(two::<T>()).mul(dot(a, b)).eqv(
            norm_sq(a.add(b)).sub(norm_sq(a.sub(b)))
        ),
{
    let na = norm_sq(a);
    let nb = norm_sq(b);
    let t = two::<T>();
    let td = t.mul(dot(a, b));

    // LHS: (t*t)*d ≡ t*td ≡ td+td
    T::axiom_mul_associative(t, t, dot(a, b));
    ring_lemmas::lemma_mul_two::<T>(td);
    T::axiom_eqv_symmetric(td.add(td), t.mul(td));
    T::axiom_eqv_transitive(t.mul(t).mul(dot(a, b)), t.mul(td), td.add(td));

    // Show norm_sq(a-b) + (td+td) ≡ norm_sq(a+b) via rearrangement
    lemma_norm_sq_sub_expand(a, b);
    T::axiom_eqv_reflexive(td.add(td));
    additive_group_lemmas::lemma_add_congruence::<T>(
        norm_sq(a.sub(b)), na.sub(td).add(nb), td.add(td), td.add(td),
    );

    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(na.sub(td), nb, td, td);
    T::axiom_eqv_transitive(
        norm_sq(a.sub(b)).add(td.add(td)),
        na.sub(td).add(nb).add(td.add(td)),
        na.sub(td).add(td).add(nb.add(td)),
    );

    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(na, td);
    T::axiom_add_commutative(nb, td);
    additive_group_lemmas::lemma_add_congruence::<T>(
        na.sub(td).add(td), na, nb.add(td), td.add(nb),
    );
    T::axiom_eqv_transitive(
        norm_sq(a.sub(b)).add(td.add(td)),
        na.sub(td).add(td).add(nb.add(td)),
        na.add(td.add(nb)),
    );

    T::axiom_add_associative(na, td, nb);
    T::axiom_eqv_symmetric(na.add(td).add(nb), na.add(td.add(nb)));
    T::axiom_eqv_transitive(
        norm_sq(a.sub(b)).add(td.add(td)),
        na.add(td.add(nb)),
        na.add(td).add(nb),
    );

    lemma_norm_sq_add_expand(a, b);
    T::axiom_eqv_symmetric(norm_sq(a.add(b)), na.add(td).add(nb));
    T::axiom_eqv_transitive(
        norm_sq(a.sub(b)).add(td.add(td)),
        na.add(td).add(nb),
        norm_sq(a.add(b)),
    );

    // Derive: td+td ≡ norm_sq(a+b) - norm_sq(a-b)
    // First get (td+td) + norm_sq(a-b) ≡ norm_sq(a+b)
    T::axiom_add_commutative(norm_sq(a.sub(b)), td.add(td));
    T::axiom_eqv_symmetric(
        norm_sq(a.sub(b)).add(td.add(td)),
        td.add(td).add(norm_sq(a.sub(b))),
    );
    T::axiom_eqv_transitive(
        td.add(td).add(norm_sq(a.sub(b))),
        norm_sq(a.sub(b)).add(td.add(td)),
        norm_sq(a.add(b)),
    );
    // norm_sq(a+b) ≡ (td+td) + norm_sq(a-b)
    T::axiom_eqv_symmetric(
        td.add(td).add(norm_sq(a.sub(b))), norm_sq(a.add(b)),
    );
    T::axiom_eqv_reflexive(norm_sq(a.sub(b)));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        norm_sq(a.add(b)), td.add(td).add(norm_sq(a.sub(b))),
        norm_sq(a.sub(b)), norm_sq(a.sub(b)),
    );
    additive_group_lemmas::lemma_add_then_sub_cancel::<T>(td.add(td), norm_sq(a.sub(b)));
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)).sub(norm_sq(a.sub(b))),
        td.add(td).add(norm_sq(a.sub(b))).sub(norm_sq(a.sub(b))),
        td.add(td),
    );

    // Chain: (t*t)*d ≡ td+td ≡ norm_sq(a+b) - norm_sq(a-b)
    T::axiom_eqv_symmetric(
        norm_sq(a.add(b)).sub(norm_sq(a.sub(b))), td.add(td),
    );
    T::axiom_eqv_transitive(
        t.mul(t).mul(dot(a, b)), td.add(td),
        norm_sq(a.add(b)).sub(norm_sq(a.sub(b))),
    );
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

// ---------------------------------------------------------------------------
// Projection / rejection
// ---------------------------------------------------------------------------

/// Projection of a onto b
pub open spec fn proj<T: OrderedField>(a: Vec2<T>, b: Vec2<T>) -> Vec2<T> {
    scale(dot(a, b).div(norm_sq(b)), b)
}

/// Rejection of a from b (component of a orthogonal to b)
pub open spec fn rej<T: OrderedField>(a: Vec2<T>, b: Vec2<T>) -> Vec2<T> {
    a.sub(proj(a, b))
}

/// dot(a.neg(), b) ≡ dot(a, b).neg()
proof fn lemma_dot_neg_left<T: Ring>(a: Vec2<T>, b: Vec2<T>)
    ensures
        dot(a.neg(), b).eqv(dot(a, b).neg()),
{
    lemma_dot_commutative(a.neg(), b);
    lemma_dot_neg_right(b, a);
    lemma_dot_commutative(b, a);
    additive_group_lemmas::lemma_neg_congruence::<T>(dot(b, a), dot(a, b));
    T::axiom_eqv_transitive(
        dot(a.neg(), b), dot(b, a.neg()), dot(b, a).neg(),
    );
    T::axiom_eqv_transitive(
        dot(a.neg(), b), dot(b, a).neg(), dot(a, b).neg(),
    );
}

/// dot(proj(a, b), b) ≡ dot(a, b) when norm_sq(b) ≢ 0
proof fn lemma_dot_proj<T: OrderedField>(a: Vec2<T>, b: Vec2<T>)
    requires
        !norm_sq(b).eqv(T::zero()),
    ensures
        dot(proj(a, b), b).eqv(dot(a, b)),
{
    let d = dot(a, b);
    let n = norm_sq(b);
    // dot(scale(d/n, b), b) ≡ (d/n) * dot(b, b) = (d/n) * n
    lemma_dot_scale_left(d.div(n), b, b);
    // (d/n) * n ≡ d
    field_lemmas::lemma_div_mul_cancel::<T>(d, n);
    T::axiom_eqv_transitive(dot(proj(a, b), b), d.div(n).mul(n), d);
}

/// proj(a, b) + rej(a, b) ≡ a
pub proof fn lemma_proj_rej_decomposition<T: OrderedField>(a: Vec2<T>, b: Vec2<T>)
    requires
        !norm_sq(b).eqv(T::zero()),
    ensures
        proj(a, b).add(rej(a, b)).eqv(a),
{
    let p = proj(a, b);
    // proj + rej = proj + (a - proj) ≡ (a - proj) + proj ≡ a
    Vec2::<T>::axiom_add_commutative(p, a.sub(p));
    additive_group_lemmas::lemma_sub_then_add_cancel::<Vec2<T>>(a, p);
    Vec2::<T>::axiom_eqv_transitive(
        p.add(a.sub(p)), a.sub(p).add(p), a,
    );
}

/// dot(rej(a, b), b) ≡ 0
pub proof fn lemma_rej_orthogonal<T: OrderedField>(a: Vec2<T>, b: Vec2<T>)
    requires
        !norm_sq(b).eqv(T::zero()),
    ensures
        dot(rej(a, b), b).eqv(T::zero()),
{
    let d = dot(a, b);
    let n = norm_sq(b);
    let p = proj(a, b);

    // Step 1: a.sub(p) ≡ a.add(p.neg())
    Vec2::<T>::axiom_sub_is_add_neg(a, p);
    Vec2::<T>::axiom_eqv_reflexive(b);
    lemma_dot_congruence(a.sub(p), a.add(p.neg()), b, b);

    // Step 2: dot(a.add(p.neg()), b) ≡ dot(a,b) + dot(p.neg(), b)
    lemma_dot_distributes_left(a, p.neg(), b);
    T::axiom_eqv_transitive(
        dot(a.sub(p), b),
        dot(a.add(p.neg()), b),
        d.add(dot(p.neg(), b)),
    );

    // Step 3: dot(p.neg(), b) ≡ dot(p, b).neg() ≡ d.neg()
    lemma_dot_neg_left(p, b);
    lemma_dot_proj(a, b);
    additive_group_lemmas::lemma_neg_congruence::<T>(dot(p, b), d);
    T::axiom_eqv_transitive(dot(p.neg(), b), dot(p, b).neg(), d.neg());

    // Step 4: d + dot(p.neg(), b) ≡ d + d.neg()
    T::axiom_eqv_reflexive(d);
    additive_group_lemmas::lemma_add_congruence::<T>(
        d, d, dot(p.neg(), b), d.neg(),
    );
    T::axiom_eqv_transitive(
        dot(a.sub(p), b),
        d.add(dot(p.neg(), b)),
        d.add(d.neg()),
    );

    // Step 5: d + d.neg() ≡ 0
    T::axiom_add_inverse_right(d);
    T::axiom_eqv_transitive(dot(a.sub(p), b), d.add(d.neg()), T::zero());
}

/// norm_sq(a) ≡ norm_sq(proj(a,b)) + norm_sq(rej(a,b))
pub proof fn lemma_proj_rej_pythagorean<T: OrderedField>(a: Vec2<T>, b: Vec2<T>)
    requires
        !norm_sq(b).eqv(T::zero()),
    ensures
        norm_sq(a).eqv(
            norm_sq(proj(a, b)).add(norm_sq(rej(a, b)))
        ),
{
    let p = proj(a, b);
    let r = rej(a, b);

    // Show dot(p, r) ≡ 0 via dot(r, p) ≡ 0
    // dot(r, b) ≡ 0 from rej_orthogonal
    lemma_rej_orthogonal(a, b);
    // dot(r, proj) = dot(r, scale(d/n, b)) ≡ (d/n) * dot(r, b) via dot_scale_right
    lemma_dot_scale_right(dot(a, b).div(norm_sq(b)), r, b);
    // (d/n) * dot(r, b) ≡ (d/n) * 0
    ring_lemmas::lemma_mul_congruence_right::<T>(
        dot(a, b).div(norm_sq(b)), dot(r, b), T::zero(),
    );
    T::axiom_eqv_transitive(
        dot(r, p),
        dot(a, b).div(norm_sq(b)).mul(dot(r, b)),
        dot(a, b).div(norm_sq(b)).mul(T::zero()),
    );
    // (d/n) * 0 ≡ 0
    T::axiom_mul_zero_right(dot(a, b).div(norm_sq(b)));
    T::axiom_eqv_transitive(
        dot(r, p),
        dot(a, b).div(norm_sq(b)).mul(T::zero()),
        T::zero(),
    );

    // dot(p, r) ≡ dot(r, p) ≡ 0
    lemma_dot_commutative(p, r);
    T::axiom_eqv_transitive(dot(p, r), dot(r, p), T::zero());

    // Apply pythagorean: norm_sq(p + r) ≡ norm_sq(p) + norm_sq(r)
    lemma_pythagorean(p, r);

    // norm_sq(a) ≡ norm_sq(p + r) via a ≡ p + r
    lemma_proj_rej_decomposition(a, b);
    Vec2::<T>::axiom_eqv_symmetric(p.add(r), a);
    Vec2::<T>::axiom_eqv_reflexive(a);
    lemma_dot_congruence(a, p.add(r), a, p.add(r));

    // Chain: norm_sq(a) ≡ norm_sq(p+r) ≡ norm_sq(p) + norm_sq(r)
    T::axiom_eqv_transitive(
        norm_sq(a), norm_sq(p.add(r)),
        norm_sq(p).add(norm_sq(r)),
    );
}

/// proj(proj(a, b), b) ≡ proj(a, b)
pub proof fn lemma_proj_idempotent<T: OrderedField>(a: Vec2<T>, b: Vec2<T>)
    requires
        !norm_sq(b).eqv(T::zero()),
    ensures
        proj(proj(a, b), b).eqv(proj(a, b)),
{
    let d = dot(a, b);
    let n = norm_sq(b);
    let p = proj(a, b);

    // dot(proj(a,b), b) ≡ d
    lemma_dot_proj(a, b);

    // dot(proj(a,b), b).div(n) ≡ d.div(n) via div congruence
    T::axiom_div_is_mul_recip(dot(p, b), n);
    T::axiom_div_is_mul_recip(d, n);
    T::axiom_mul_congruence_left(dot(p, b), d, n.recip());
    T::axiom_eqv_transitive(
        dot(p, b).div(n), dot(p, b).mul(n.recip()), d.mul(n.recip()),
    );
    T::axiom_eqv_symmetric(d.div(n), d.mul(n.recip()));
    T::axiom_eqv_transitive(dot(p, b).div(n), d.mul(n.recip()), d.div(n));

    // scale(dot(p,b)/n, b) ≡ scale(d/n, b) = proj(a, b)  (component-level scalar congruence)
    T::axiom_mul_congruence_left(dot(p, b).div(n), d.div(n), b.x);
    T::axiom_mul_congruence_left(dot(p, b).div(n), d.div(n), b.y);
}

/// proj(a, b) ≡ zero when dot(a, b) ≡ 0
pub proof fn lemma_proj_zero_when_orthogonal<T: OrderedField>(a: Vec2<T>, b: Vec2<T>)
    requires
        dot(a, b).eqv(T::zero()),
        !norm_sq(b).eqv(T::zero()),
    ensures
        proj(a, b).eqv(Vec2 { x: T::zero(), y: T::zero() }),
{
    let d = dot(a, b);
    let n = norm_sq(b);

    // d/n ≡ 0 since d ≡ 0
    T::axiom_div_is_mul_recip(d, n);
    T::axiom_mul_congruence_left(d, T::zero(), n.recip());
    ring_lemmas::lemma_mul_zero_left::<T>(n.recip());
    T::axiom_eqv_transitive(d.div(n), d.mul(n.recip()), T::zero().mul(n.recip()));
    T::axiom_eqv_transitive(d.div(n), T::zero().mul(n.recip()), T::zero());

    // scale(d/n, b) ≡ scale(0, b) ≡ zero
    T::axiom_mul_congruence_left(d.div(n), T::zero(), b.x);
    T::axiom_mul_congruence_left(d.div(n), T::zero(), b.y);
    ring_lemmas::lemma_mul_zero_left::<T>(b.x);
    ring_lemmas::lemma_mul_zero_left::<T>(b.y);
    T::axiom_eqv_transitive(d.div(n).mul(b.x), T::zero().mul(b.x), T::zero());
    T::axiom_eqv_transitive(d.div(n).mul(b.y), T::zero().mul(b.y), T::zero());
}

// ---------------------------------------------------------------------------
// Componentwise min/max
// ---------------------------------------------------------------------------

pub open spec fn cwise_min<T: OrderedRing>(a: Vec2<T>, b: Vec2<T>) -> Vec2<T> {
    Vec2 { x: min_max::min(a.x, b.x), y: min_max::min(a.y, b.y) }
}

pub open spec fn cwise_max<T: OrderedRing>(a: Vec2<T>, b: Vec2<T>) -> Vec2<T> {
    Vec2 { x: min_max::max(a.x, b.x), y: min_max::max(a.y, b.y) }
}

/// Each component of cwise_min(a, b) ≤ corresponding component of a
pub proof fn lemma_cwise_min_le_left<T: OrderedRing>(a: Vec2<T>, b: Vec2<T>)
    ensures
        cwise_min(a, b).x.le(a.x),
        cwise_min(a, b).y.le(a.y),
{
    min_max::lemma_min_le_left::<T>(a.x, b.x);
    min_max::lemma_min_le_left::<T>(a.y, b.y);
}

/// Each component of cwise_min(a, b) ≤ corresponding component of b
pub proof fn lemma_cwise_min_le_right<T: OrderedRing>(a: Vec2<T>, b: Vec2<T>)
    ensures
        cwise_min(a, b).x.le(b.x),
        cwise_min(a, b).y.le(b.y),
{
    min_max::lemma_min_le_right::<T>(a.x, b.x);
    min_max::lemma_min_le_right::<T>(a.y, b.y);
}

/// Each component of a ≤ corresponding component of cwise_max(a, b)
pub proof fn lemma_cwise_max_ge_left<T: OrderedRing>(a: Vec2<T>, b: Vec2<T>)
    ensures
        a.x.le(cwise_max(a, b).x),
        a.y.le(cwise_max(a, b).y),
{
    min_max::lemma_max_ge_left::<T>(a.x, b.x);
    min_max::lemma_max_ge_left::<T>(a.y, b.y);
}

/// Each component of b ≤ corresponding component of cwise_max(a, b)
pub proof fn lemma_cwise_max_ge_right<T: OrderedRing>(a: Vec2<T>, b: Vec2<T>)
    ensures
        b.x.le(cwise_max(a, b).x),
        b.y.le(cwise_max(a, b).y),
{
    min_max::lemma_max_ge_right::<T>(a.x, b.x);
    min_max::lemma_max_ge_right::<T>(a.y, b.y);
}

} // verus!
