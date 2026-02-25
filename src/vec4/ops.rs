use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_commutative_monoid_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::inequalities;
use verus_algebra::min_max;
use verus_algebra::convex::two;
use super::Vec4;

verus! {

// ---------------------------------------------------------------------------
// Spec functions
// ---------------------------------------------------------------------------

pub open spec fn scale<T: Ring>(s: T, v: Vec4<T>) -> Vec4<T> {
    Vec4 { x: s.mul(v.x), y: s.mul(v.y), z: s.mul(v.z), w: s.mul(v.w) }
}

pub open spec fn dot<T: Ring>(a: Vec4<T>, b: Vec4<T>) -> T {
    a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)).add(a.w.mul(b.w))
}

pub open spec fn norm_sq<T: Ring>(v: Vec4<T>) -> T {
    dot(v, v)
}

pub open spec fn lerp<T: Ring>(a: Vec4<T>, b: Vec4<T>, t: T) -> Vec4<T> {
    scale(T::one().sub(t), a).add(scale(t, b))
}

// ---------------------------------------------------------------------------
// Scale lemmas
// ---------------------------------------------------------------------------

/// scale(s, a + b) ≡ scale(s, a) + scale(s, b)
pub proof fn lemma_scale_distributes_over_add<T: Ring>(s: T, a: Vec4<T>, b: Vec4<T>)
    ensures
        scale(s, a.add(b)).eqv(scale(s, a).add(scale(s, b))),
{
    T::axiom_mul_distributes_left(s, a.x, b.x);
    T::axiom_mul_distributes_left(s, a.y, b.y);
    T::axiom_mul_distributes_left(s, a.z, b.z);
    T::axiom_mul_distributes_left(s, a.w, b.w);
}

/// scale(s + t, a) ≡ scale(s, a) + scale(t, a)
pub proof fn lemma_scale_add_distributes<T: Ring>(s: T, t: T, a: Vec4<T>)
    ensures
        scale(s.add(t), a).eqv(scale(s, a).add(scale(t, a))),
{
    ring_lemmas::lemma_mul_distributes_right::<T>(s, t, a.x);
    ring_lemmas::lemma_mul_distributes_right::<T>(s, t, a.y);
    ring_lemmas::lemma_mul_distributes_right::<T>(s, t, a.z);
    ring_lemmas::lemma_mul_distributes_right::<T>(s, t, a.w);
}

/// scale(1, a) ≡ a
pub proof fn lemma_scale_identity<T: Ring>(a: Vec4<T>)
    ensures
        scale(T::one(), a).eqv(a),
{
    ring_lemmas::lemma_mul_one_left::<T>(a.x);
    ring_lemmas::lemma_mul_one_left::<T>(a.y);
    ring_lemmas::lemma_mul_one_left::<T>(a.z);
    ring_lemmas::lemma_mul_one_left::<T>(a.w);
}

/// scale(0, a) ≡ zero
pub proof fn lemma_scale_zero_scalar<T: Ring>(a: Vec4<T>)
    ensures
        scale(T::zero(), a).eqv(
            Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: T::zero() }
        ),
{
    ring_lemmas::lemma_mul_zero_left::<T>(a.x);
    ring_lemmas::lemma_mul_zero_left::<T>(a.y);
    ring_lemmas::lemma_mul_zero_left::<T>(a.z);
    ring_lemmas::lemma_mul_zero_left::<T>(a.w);
}

/// scale(s, zero) ≡ zero
pub proof fn lemma_scale_zero_vec<T: Ring>(s: T)
    ensures
        scale(s, Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: T::zero() })
            .eqv(Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: T::zero() }),
{
    T::axiom_mul_zero_right(s);
}

/// a ≡ b implies scale(s, a) ≡ scale(s, b)
pub proof fn lemma_scale_congruence<T: Ring>(s: T, a: Vec4<T>, b: Vec4<T>)
    requires
        a.eqv(b),
    ensures
        scale(s, a).eqv(scale(s, b)),
{
    ring_lemmas::lemma_mul_congruence_right::<T>(s, a.x, b.x);
    ring_lemmas::lemma_mul_congruence_right::<T>(s, a.y, b.y);
    ring_lemmas::lemma_mul_congruence_right::<T>(s, a.z, b.z);
    ring_lemmas::lemma_mul_congruence_right::<T>(s, a.w, b.w);
}

/// scale(s, scale(t, a)) ≡ scale(s * t, a)
pub proof fn lemma_scale_associative<T: Ring>(s: T, t: T, a: Vec4<T>)
    ensures
        scale(s, scale(t, a)).eqv(scale(s.mul(t), a)),
{
    T::axiom_mul_associative(s, t, a.x);
    T::axiom_eqv_symmetric(s.mul(t).mul(a.x), s.mul(t.mul(a.x)));
    T::axiom_mul_associative(s, t, a.y);
    T::axiom_eqv_symmetric(s.mul(t).mul(a.y), s.mul(t.mul(a.y)));
    T::axiom_mul_associative(s, t, a.z);
    T::axiom_eqv_symmetric(s.mul(t).mul(a.z), s.mul(t.mul(a.z)));
    T::axiom_mul_associative(s, t, a.w);
    T::axiom_eqv_symmetric(s.mul(t).mul(a.w), s.mul(t.mul(a.w)));
}

/// scale(-s, a) ≡ -scale(s, a)
pub proof fn lemma_scale_neg_scalar<T: Ring>(s: T, a: Vec4<T>)
    ensures
        scale(s.neg(), a).eqv(scale(s, a).neg()),
{
    ring_lemmas::lemma_mul_neg_left::<T>(s, a.x);
    ring_lemmas::lemma_mul_neg_left::<T>(s, a.y);
    ring_lemmas::lemma_mul_neg_left::<T>(s, a.z);
    ring_lemmas::lemma_mul_neg_left::<T>(s, a.w);
}

/// scale(s, -a) ≡ -scale(s, a)
pub proof fn lemma_scale_neg_vec<T: Ring>(s: T, a: Vec4<T>)
    ensures
        scale(s, a.neg()).eqv(scale(s, a).neg()),
{
    ring_lemmas::lemma_mul_neg_right::<T>(s, a.x);
    ring_lemmas::lemma_mul_neg_right::<T>(s, a.y);
    ring_lemmas::lemma_mul_neg_right::<T>(s, a.z);
    ring_lemmas::lemma_mul_neg_right::<T>(s, a.w);
}

/// scale(s, a - b) ≡ scale(s, a) - scale(s, b)
pub proof fn lemma_scale_sub_distributes<T: Ring>(s: T, a: Vec4<T>, b: Vec4<T>)
    ensures
        scale(s, a.sub(b)).eqv(scale(s, a).sub(scale(s, b))),
{
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.x, b.x);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.y, b.y);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.z, b.z);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.w, b.w);
}

// ---------------------------------------------------------------------------
// Dot lemmas
// ---------------------------------------------------------------------------

/// dot(a, b) ≡ dot(b, a)
pub proof fn lemma_dot_commutative<T: Ring>(a: Vec4<T>, b: Vec4<T>)
    ensures
        dot(a, b).eqv(dot(b, a)),
{
    T::axiom_mul_commutative(a.x, b.x);
    T::axiom_mul_commutative(a.y, b.y);
    T::axiom_mul_commutative(a.z, b.z);
    T::axiom_mul_commutative(a.w, b.w);
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(b.x), b.x.mul(a.x),
        a.y.mul(b.y), b.y.mul(a.y),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(b.x).add(a.y.mul(b.y)),
        b.x.mul(a.x).add(b.y.mul(a.y)),
        a.z.mul(b.z),
        b.z.mul(a.z),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)),
        b.x.mul(a.x).add(b.y.mul(a.y)).add(b.z.mul(a.z)),
        a.w.mul(b.w),
        b.w.mul(a.w),
    );
}

/// dot(a, zero) ≡ 0
pub proof fn lemma_dot_zero_right<T: Ring>(a: Vec4<T>)
    ensures
        dot(a, Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: T::zero() })
            .eqv(T::zero()),
{
    T::axiom_mul_zero_right(a.x);
    T::axiom_mul_zero_right(a.y);
    T::axiom_mul_zero_right(a.z);
    T::axiom_mul_zero_right(a.w);
    // a.x*0 + a.y*0 ≡ 0 + 0
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(T::zero()), T::zero(),
        a.y.mul(T::zero()), T::zero(),
    );
    // 0 + 0 ≡ 0
    T::axiom_add_zero_right(T::zero());
    // a.x*0 + a.y*0 ≡ 0
    T::axiom_eqv_transitive(
        a.x.mul(T::zero()).add(a.y.mul(T::zero())),
        T::zero().add(T::zero()),
        T::zero(),
    );
    // (a.x*0 + a.y*0) + a.z*0 ≡ 0 + 0
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(T::zero()).add(a.y.mul(T::zero())), T::zero(),
        a.z.mul(T::zero()), T::zero(),
    );
    // (a.x*0 + a.y*0) + a.z*0 ≡ 0
    T::axiom_eqv_transitive(
        a.x.mul(T::zero()).add(a.y.mul(T::zero())).add(a.z.mul(T::zero())),
        T::zero().add(T::zero()),
        T::zero(),
    );
    // ((a.x*0 + a.y*0) + a.z*0) + a.w*0 ≡ 0 + 0
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(T::zero()).add(a.y.mul(T::zero())).add(a.z.mul(T::zero())), T::zero(),
        a.w.mul(T::zero()), T::zero(),
    );
    // ((a.x*0 + a.y*0) + a.z*0) + a.w*0 ≡ 0
    T::axiom_eqv_transitive(
        a.x.mul(T::zero()).add(a.y.mul(T::zero())).add(a.z.mul(T::zero())).add(a.w.mul(T::zero())),
        T::zero().add(T::zero()),
        T::zero(),
    );
}

/// dot(zero, a) ≡ 0
pub proof fn lemma_dot_zero_left<T: Ring>(a: Vec4<T>)
    ensures
        dot(Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: T::zero() }, a)
            .eqv(T::zero()),
{
    ring_lemmas::lemma_mul_zero_left::<T>(a.x);
    ring_lemmas::lemma_mul_zero_left::<T>(a.y);
    ring_lemmas::lemma_mul_zero_left::<T>(a.z);
    ring_lemmas::lemma_mul_zero_left::<T>(a.w);
    // 0*a.x + 0*a.y ≡ 0 + 0
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(a.x), T::zero(),
        T::zero().mul(a.y), T::zero(),
    );
    // 0 + 0 ≡ 0
    T::axiom_add_zero_right(T::zero());
    // 0*a.x + 0*a.y ≡ 0
    T::axiom_eqv_transitive(
        T::zero().mul(a.x).add(T::zero().mul(a.y)),
        T::zero().add(T::zero()),
        T::zero(),
    );
    // (0*a.x + 0*a.y) + 0*a.z ≡ 0 + 0
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(a.x).add(T::zero().mul(a.y)), T::zero(),
        T::zero().mul(a.z), T::zero(),
    );
    // (0*a.x + 0*a.y) + 0*a.z ≡ 0
    T::axiom_eqv_transitive(
        T::zero().mul(a.x).add(T::zero().mul(a.y)).add(T::zero().mul(a.z)),
        T::zero().add(T::zero()),
        T::zero(),
    );
    // ((0*a.x + 0*a.y) + 0*a.z) + 0*a.w ≡ 0 + 0
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        T::zero().mul(a.x).add(T::zero().mul(a.y)).add(T::zero().mul(a.z)), T::zero(),
        T::zero().mul(a.w), T::zero(),
    );
    // ((0*a.x + 0*a.y) + 0*a.z) + 0*a.w ≡ 0
    T::axiom_eqv_transitive(
        T::zero().mul(a.x).add(T::zero().mul(a.y)).add(T::zero().mul(a.z)).add(T::zero().mul(a.w)),
        T::zero().add(T::zero()),
        T::zero(),
    );
}

/// dot(a, b + c) ≡ dot(a, b) + dot(a, c)
pub proof fn lemma_dot_distributes_right<T: Ring>(a: Vec4<T>, b: Vec4<T>, c: Vec4<T>)
    ensures
        dot(a, b.add(c)).eqv(dot(a, b).add(dot(a, c))),
{
    // Distribute each component
    T::axiom_mul_distributes_left(a.x, b.x, c.x);
    T::axiom_mul_distributes_left(a.y, b.y, c.y);
    T::axiom_mul_distributes_left(a.z, b.z, c.z);
    T::axiom_mul_distributes_left(a.w, b.w, c.w);

    // Propagate first two
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(b.x.add(c.x)), a.x.mul(b.x).add(a.x.mul(c.x)),
        a.y.mul(b.y.add(c.y)), a.y.mul(b.y).add(a.y.mul(c.y)),
    );
    // Propagate with third
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(b.x.add(c.x)).add(a.y.mul(b.y.add(c.y))),
        a.x.mul(b.x).add(a.x.mul(c.x)).add(a.y.mul(b.y).add(a.y.mul(c.y))),
        a.z.mul(b.z.add(c.z)),
        a.z.mul(b.z).add(a.z.mul(c.z)),
    );
    // Propagate with fourth
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(b.x.add(c.x)).add(a.y.mul(b.y.add(c.y))).add(a.z.mul(b.z.add(c.z))),
        a.x.mul(b.x).add(a.x.mul(c.x)).add(a.y.mul(b.y).add(a.y.mul(c.y))).add(a.z.mul(b.z).add(a.z.mul(c.z))),
        a.w.mul(b.w.add(c.w)),
        a.w.mul(b.w).add(a.w.mul(c.w)),
    );
    // Now: LHS ≡ (((axbx+axcx)+(ayby+aycy))+(azbz+azcz))+(awbw+awcw)

    // Rearrange first pair: (axbx+axcx)+(ayby+aycy) ≡ (axbx+ayby)+(axcx+aycy)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.x.mul(b.x), a.x.mul(c.x), a.y.mul(b.y), a.y.mul(c.y),
    );
    // Propagate through z add
    T::axiom_add_congruence_left(
        a.x.mul(b.x).add(a.x.mul(c.x)).add(a.y.mul(b.y).add(a.y.mul(c.y))),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.x.mul(c.x).add(a.y.mul(c.y))),
        a.z.mul(b.z).add(a.z.mul(c.z)),
    );
    // Propagate through w add
    T::axiom_add_congruence_left(
        a.x.mul(b.x).add(a.x.mul(c.x)).add(a.y.mul(b.y).add(a.y.mul(c.y))).add(a.z.mul(b.z).add(a.z.mul(c.z))),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.x.mul(c.x).add(a.y.mul(c.y))).add(a.z.mul(b.z).add(a.z.mul(c.z))),
        a.w.mul(b.w).add(a.w.mul(c.w)),
    );

    // Rearrange second pair: ((axbx+ayby)+(axcx+aycy))+(azbz+azcz) ≡ ((axbx+ayby)+azbz)+((axcx+aycy)+azcz)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.x.mul(b.x).add(a.y.mul(b.y)),
        a.x.mul(c.x).add(a.y.mul(c.y)),
        a.z.mul(b.z),
        a.z.mul(c.z),
    );
    // Propagate through w add
    T::axiom_add_congruence_left(
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.x.mul(c.x).add(a.y.mul(c.y))).add(a.z.mul(b.z).add(a.z.mul(c.z))),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)).add(a.x.mul(c.x).add(a.y.mul(c.y)).add(a.z.mul(c.z))),
        a.w.mul(b.w).add(a.w.mul(c.w)),
    );

    // Rearrange third pair: (dot3(a,b)+dot3(a,c))+(awbw+awcw) ≡ dot(a,b)+dot(a,c)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)),
        a.x.mul(c.x).add(a.y.mul(c.y)).add(a.z.mul(c.z)),
        a.w.mul(b.w),
        a.w.mul(c.w),
    );

    // Chain all transitivities: LHS ≡ E1 ≡ E2 ≡ E3 ≡ RHS
    T::axiom_eqv_transitive(
        dot(a, b.add(c)),
        a.x.mul(b.x).add(a.x.mul(c.x)).add(a.y.mul(b.y).add(a.y.mul(c.y))).add(a.z.mul(b.z).add(a.z.mul(c.z))).add(a.w.mul(b.w).add(a.w.mul(c.w))),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.x.mul(c.x).add(a.y.mul(c.y))).add(a.z.mul(b.z).add(a.z.mul(c.z))).add(a.w.mul(b.w).add(a.w.mul(c.w))),
    );
    T::axiom_eqv_transitive(
        dot(a, b.add(c)),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.x.mul(c.x).add(a.y.mul(c.y))).add(a.z.mul(b.z).add(a.z.mul(c.z))).add(a.w.mul(b.w).add(a.w.mul(c.w))),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)).add(a.x.mul(c.x).add(a.y.mul(c.y)).add(a.z.mul(c.z))).add(a.w.mul(b.w).add(a.w.mul(c.w))),
    );
    T::axiom_eqv_transitive(
        dot(a, b.add(c)),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)).add(a.x.mul(c.x).add(a.y.mul(c.y)).add(a.z.mul(c.z))).add(a.w.mul(b.w).add(a.w.mul(c.w))),
        dot(a, b).add(dot(a, c)),
    );
}

/// dot(a + b, c) ≡ dot(a, c) + dot(b, c)
pub proof fn lemma_dot_distributes_left<T: Ring>(a: Vec4<T>, b: Vec4<T>, c: Vec4<T>)
    ensures
        dot(a.add(b), c).eqv(dot(a, c).add(dot(b, c))),
{
    // Distribute each component
    ring_lemmas::lemma_mul_distributes_right::<T>(a.x, b.x, c.x);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.y, b.y, c.y);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.z, b.z, c.z);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.w, b.w, c.w);

    // Propagate through additions
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.add(b.x).mul(c.x), a.x.mul(c.x).add(b.x.mul(c.x)),
        a.y.add(b.y).mul(c.y), a.y.mul(c.y).add(b.y.mul(c.y)),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.add(b.x).mul(c.x).add(a.y.add(b.y).mul(c.y)),
        a.x.mul(c.x).add(b.x.mul(c.x)).add(a.y.mul(c.y).add(b.y.mul(c.y))),
        a.z.add(b.z).mul(c.z),
        a.z.mul(c.z).add(b.z.mul(c.z)),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.add(b.x).mul(c.x).add(a.y.add(b.y).mul(c.y)).add(a.z.add(b.z).mul(c.z)),
        a.x.mul(c.x).add(b.x.mul(c.x)).add(a.y.mul(c.y).add(b.y.mul(c.y))).add(a.z.mul(c.z).add(b.z.mul(c.z))),
        a.w.add(b.w).mul(c.w),
        a.w.mul(c.w).add(b.w.mul(c.w)),
    );

    // Rearrange: same 3-stage as distributes_right
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.x.mul(c.x), b.x.mul(c.x), a.y.mul(c.y), b.y.mul(c.y),
    );
    T::axiom_add_congruence_left(
        a.x.mul(c.x).add(b.x.mul(c.x)).add(a.y.mul(c.y).add(b.y.mul(c.y))),
        a.x.mul(c.x).add(a.y.mul(c.y)).add(b.x.mul(c.x).add(b.y.mul(c.y))),
        a.z.mul(c.z).add(b.z.mul(c.z)),
    );
    T::axiom_add_congruence_left(
        a.x.mul(c.x).add(b.x.mul(c.x)).add(a.y.mul(c.y).add(b.y.mul(c.y))).add(a.z.mul(c.z).add(b.z.mul(c.z))),
        a.x.mul(c.x).add(a.y.mul(c.y)).add(b.x.mul(c.x).add(b.y.mul(c.y))).add(a.z.mul(c.z).add(b.z.mul(c.z))),
        a.w.mul(c.w).add(b.w.mul(c.w)),
    );

    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.x.mul(c.x).add(a.y.mul(c.y)),
        b.x.mul(c.x).add(b.y.mul(c.y)),
        a.z.mul(c.z),
        b.z.mul(c.z),
    );
    T::axiom_add_congruence_left(
        a.x.mul(c.x).add(a.y.mul(c.y)).add(b.x.mul(c.x).add(b.y.mul(c.y))).add(a.z.mul(c.z).add(b.z.mul(c.z))),
        a.x.mul(c.x).add(a.y.mul(c.y)).add(a.z.mul(c.z)).add(b.x.mul(c.x).add(b.y.mul(c.y)).add(b.z.mul(c.z))),
        a.w.mul(c.w).add(b.w.mul(c.w)),
    );

    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.x.mul(c.x).add(a.y.mul(c.y)).add(a.z.mul(c.z)),
        b.x.mul(c.x).add(b.y.mul(c.y)).add(b.z.mul(c.z)),
        a.w.mul(c.w),
        b.w.mul(c.w),
    );

    // Chain
    T::axiom_eqv_transitive(
        dot(a.add(b), c),
        a.x.mul(c.x).add(b.x.mul(c.x)).add(a.y.mul(c.y).add(b.y.mul(c.y))).add(a.z.mul(c.z).add(b.z.mul(c.z))).add(a.w.mul(c.w).add(b.w.mul(c.w))),
        a.x.mul(c.x).add(a.y.mul(c.y)).add(b.x.mul(c.x).add(b.y.mul(c.y))).add(a.z.mul(c.z).add(b.z.mul(c.z))).add(a.w.mul(c.w).add(b.w.mul(c.w))),
    );
    T::axiom_eqv_transitive(
        dot(a.add(b), c),
        a.x.mul(c.x).add(a.y.mul(c.y)).add(b.x.mul(c.x).add(b.y.mul(c.y))).add(a.z.mul(c.z).add(b.z.mul(c.z))).add(a.w.mul(c.w).add(b.w.mul(c.w))),
        a.x.mul(c.x).add(a.y.mul(c.y)).add(a.z.mul(c.z)).add(b.x.mul(c.x).add(b.y.mul(c.y)).add(b.z.mul(c.z))).add(a.w.mul(c.w).add(b.w.mul(c.w))),
    );
    T::axiom_eqv_transitive(
        dot(a.add(b), c),
        a.x.mul(c.x).add(a.y.mul(c.y)).add(a.z.mul(c.z)).add(b.x.mul(c.x).add(b.y.mul(c.y)).add(b.z.mul(c.z))).add(a.w.mul(c.w).add(b.w.mul(c.w))),
        dot(a, c).add(dot(b, c)),
    );
}

/// dot(scale(s, a), b) ≡ s * dot(a, b)
pub proof fn lemma_dot_scale_left<T: Ring>(s: T, a: Vec4<T>, b: Vec4<T>)
    ensures
        dot(scale(s, a), b).eqv(s.mul(dot(a, b))),
{
    // (s*ai)*bi ≡ s*(ai*bi) for each component
    T::axiom_mul_associative(s, a.x, b.x);
    T::axiom_mul_associative(s, a.y, b.y);
    T::axiom_mul_associative(s, a.z, b.z);
    T::axiom_mul_associative(s, a.w, b.w);

    // Propagate through additions
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        s.mul(a.x).mul(b.x), s.mul(a.x.mul(b.x)),
        s.mul(a.y).mul(b.y), s.mul(a.y.mul(b.y)),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        s.mul(a.x).mul(b.x).add(s.mul(a.y).mul(b.y)),
        s.mul(a.x.mul(b.x)).add(s.mul(a.y.mul(b.y))),
        s.mul(a.z).mul(b.z),
        s.mul(a.z.mul(b.z)),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        s.mul(a.x).mul(b.x).add(s.mul(a.y).mul(b.y)).add(s.mul(a.z).mul(b.z)),
        s.mul(a.x.mul(b.x)).add(s.mul(a.y.mul(b.y))).add(s.mul(a.z.mul(b.z))),
        s.mul(a.w).mul(b.w),
        s.mul(a.w.mul(b.w)),
    );
    // LHS ≡ s*(ax*bx) + s*(ay*by) + s*(az*bz) + s*(aw*bw)

    // Factor out s from first two: s*(ax*bx) + s*(ay*by) ≡ s*(ax*bx + ay*by)
    T::axiom_mul_distributes_left(s, a.x.mul(b.x), a.y.mul(b.y));
    T::axiom_eqv_symmetric(
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y))),
        s.mul(a.x.mul(b.x)).add(s.mul(a.y.mul(b.y))),
    );
    T::axiom_add_congruence_left(
        s.mul(a.x.mul(b.x)).add(s.mul(a.y.mul(b.y))),
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y))),
        s.mul(a.z.mul(b.z)),
    );
    T::axiom_add_congruence_left(
        s.mul(a.x.mul(b.x)).add(s.mul(a.y.mul(b.y))).add(s.mul(a.z.mul(b.z))),
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y))).add(s.mul(a.z.mul(b.z))),
        s.mul(a.w.mul(b.w)),
    );

    // Factor next: s*(ax*bx+ay*by) + s*(az*bz) ≡ s*((ax*bx+ay*by)+az*bz)
    T::axiom_mul_distributes_left(s, a.x.mul(b.x).add(a.y.mul(b.y)), a.z.mul(b.z));
    T::axiom_eqv_symmetric(
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z))),
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y))).add(s.mul(a.z.mul(b.z))),
    );
    T::axiom_add_congruence_left(
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y))).add(s.mul(a.z.mul(b.z))),
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z))),
        s.mul(a.w.mul(b.w)),
    );

    // Factor last: s*dot3(a,b) + s*(aw*bw) ≡ s*dot(a,b)
    T::axiom_mul_distributes_left(s, a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)), a.w.mul(b.w));
    T::axiom_eqv_symmetric(
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)).add(a.w.mul(b.w))),
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z))).add(s.mul(a.w.mul(b.w))),
    );

    // Chain: LHS ≡ E1 ≡ E2 ≡ E3 ≡ RHS
    T::axiom_eqv_transitive(
        dot(scale(s, a), b),
        s.mul(a.x.mul(b.x)).add(s.mul(a.y.mul(b.y))).add(s.mul(a.z.mul(b.z))).add(s.mul(a.w.mul(b.w))),
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y))).add(s.mul(a.z.mul(b.z))).add(s.mul(a.w.mul(b.w))),
    );
    T::axiom_eqv_transitive(
        dot(scale(s, a), b),
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y))).add(s.mul(a.z.mul(b.z))).add(s.mul(a.w.mul(b.w))),
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z))).add(s.mul(a.w.mul(b.w))),
    );
    T::axiom_eqv_transitive(
        dot(scale(s, a), b),
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z))).add(s.mul(a.w.mul(b.w))),
        s.mul(dot(a, b)),
    );
}

/// dot(a, scale(s, b)) ≡ s * dot(a, b)
pub proof fn lemma_dot_scale_right<T: Ring>(s: T, a: Vec4<T>, b: Vec4<T>)
    ensures
        dot(a, scale(s, b)).eqv(s.mul(dot(a, b))),
{
    lemma_dot_commutative(a, scale(s, b));
    lemma_dot_scale_left(s, b, a);
    T::axiom_eqv_transitive(
        dot(a, scale(s, b)),
        dot(scale(s, b), a),
        s.mul(dot(b, a)),
    );
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
pub proof fn lemma_dot_congruence<T: Ring>(a1: Vec4<T>, a2: Vec4<T>, b1: Vec4<T>, b2: Vec4<T>)
    requires
        a1.eqv(a2),
        b1.eqv(b2),
    ensures
        dot(a1, b1).eqv(dot(a2, b2)),
{
    ring_lemmas::lemma_mul_congruence::<T>(a1.x, a2.x, b1.x, b2.x);
    ring_lemmas::lemma_mul_congruence::<T>(a1.y, a2.y, b1.y, b2.y);
    ring_lemmas::lemma_mul_congruence::<T>(a1.z, a2.z, b1.z, b2.z);
    ring_lemmas::lemma_mul_congruence::<T>(a1.w, a2.w, b1.w, b2.w);
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a1.x.mul(b1.x), a2.x.mul(b2.x),
        a1.y.mul(b1.y), a2.y.mul(b2.y),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a1.x.mul(b1.x).add(a1.y.mul(b1.y)),
        a2.x.mul(b2.x).add(a2.y.mul(b2.y)),
        a1.z.mul(b1.z),
        a2.z.mul(b2.z),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a1.x.mul(b1.x).add(a1.y.mul(b1.y)).add(a1.z.mul(b1.z)),
        a2.x.mul(b2.x).add(a2.y.mul(b2.y)).add(a2.z.mul(b2.z)),
        a1.w.mul(b1.w),
        a2.w.mul(b2.w),
    );
}

/// dot(a, -b) ≡ -dot(a, b)
pub proof fn lemma_dot_neg_right<T: Ring>(a: Vec4<T>, b: Vec4<T>)
    ensures
        dot(a, b.neg()).eqv(dot(a, b).neg()),
{
    ring_lemmas::lemma_mul_neg_right::<T>(a.x, b.x);
    ring_lemmas::lemma_mul_neg_right::<T>(a.y, b.y);
    ring_lemmas::lemma_mul_neg_right::<T>(a.z, b.z);
    ring_lemmas::lemma_mul_neg_right::<T>(a.w, b.w);
    // LHS ≡ -(ax*bx) + -(ay*by) + -(az*bz) + -(aw*bw)
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(b.x.neg()), a.x.mul(b.x).neg(),
        a.y.mul(b.y.neg()), a.y.mul(b.y).neg(),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(b.x.neg()).add(a.y.mul(b.y.neg())),
        a.x.mul(b.x).neg().add(a.y.mul(b.y).neg()),
        a.z.mul(b.z.neg()),
        a.z.mul(b.z).neg(),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.mul(b.x.neg()).add(a.y.mul(b.y.neg())).add(a.z.mul(b.z.neg())),
        a.x.mul(b.x).neg().add(a.y.mul(b.y).neg()).add(a.z.mul(b.z).neg()),
        a.w.mul(b.w.neg()),
        a.w.mul(b.w).neg(),
    );
    // -(ax*bx) + -(ay*by) ≡ -(ax*bx + ay*by)
    additive_group_lemmas::lemma_neg_add::<T>(a.x.mul(b.x), a.y.mul(b.y));
    T::axiom_eqv_symmetric(
        a.x.mul(b.x).add(a.y.mul(b.y)).neg(),
        a.x.mul(b.x).neg().add(a.y.mul(b.y).neg()),
    );
    // -(xy) + -(xz) ≡ -(xy+xz)
    T::axiom_add_congruence_left(
        a.x.mul(b.x).neg().add(a.y.mul(b.y).neg()),
        a.x.mul(b.x).add(a.y.mul(b.y)).neg(),
        a.z.mul(b.z).neg(),
    );
    additive_group_lemmas::lemma_neg_add::<T>(a.x.mul(b.x).add(a.y.mul(b.y)), a.z.mul(b.z));
    T::axiom_eqv_symmetric(
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)).neg(),
        a.x.mul(b.x).add(a.y.mul(b.y)).neg().add(a.z.mul(b.z).neg()),
    );
    T::axiom_eqv_transitive(
        a.x.mul(b.x).neg().add(a.y.mul(b.y).neg()).add(a.z.mul(b.z).neg()),
        a.x.mul(b.x).add(a.y.mul(b.y)).neg().add(a.z.mul(b.z).neg()),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)).neg(),
    );
    // -(xyz) + -(aw*bw) ≡ -(xyz + aw*bw)
    T::axiom_add_congruence_left(
        a.x.mul(b.x).neg().add(a.y.mul(b.y).neg()).add(a.z.mul(b.z).neg()),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)).neg(),
        a.w.mul(b.w).neg(),
    );
    additive_group_lemmas::lemma_neg_add::<T>(
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)),
        a.w.mul(b.w),
    );
    T::axiom_eqv_symmetric(
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)).add(a.w.mul(b.w)).neg(),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)).neg().add(a.w.mul(b.w).neg()),
    );
    // Chain from LHS to RHS
    T::axiom_eqv_transitive(
        dot(a, b.neg()),
        a.x.mul(b.x).neg().add(a.y.mul(b.y).neg()).add(a.z.mul(b.z).neg()).add(a.w.mul(b.w).neg()),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)).neg().add(a.w.mul(b.w).neg()),
    );
    T::axiom_eqv_transitive(
        dot(a, b.neg()),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z)).neg().add(a.w.mul(b.w).neg()),
        dot(a, b).neg(),
    );
}

// ---------------------------------------------------------------------------
// Norm-squared lemmas
// ---------------------------------------------------------------------------

/// a ≡ b implies norm_sq(a) ≡ norm_sq(b)
pub proof fn lemma_norm_sq_congruence<T: Ring>(a: Vec4<T>, b: Vec4<T>)
    requires
        a.eqv(b),
    ensures
        norm_sq(a).eqv(norm_sq(b)),
{
    lemma_dot_congruence(a, b, a, b);
}

/// norm_sq(scale(s, v)) ≡ s*s * norm_sq(v)
pub proof fn lemma_norm_sq_scale<T: Ring>(s: T, v: Vec4<T>)
    ensures
        norm_sq(scale(s, v)).eqv(s.mul(s).mul(norm_sq(v))),
{
    lemma_dot_scale_left(s, v, scale(s, v));
    lemma_dot_scale_right(s, v, v);
    ring_lemmas::lemma_mul_congruence_right::<T>(s, dot(v, scale(s, v)), s.mul(dot(v, v)));
    T::axiom_eqv_transitive(
        norm_sq(scale(s, v)),
        s.mul(dot(v, scale(s, v))),
        s.mul(s.mul(dot(v, v))),
    );
    T::axiom_mul_associative(s, s, dot(v, v));
    T::axiom_eqv_symmetric(s.mul(s).mul(dot(v, v)), s.mul(s.mul(dot(v, v))));
    T::axiom_eqv_transitive(
        norm_sq(scale(s, v)),
        s.mul(s.mul(dot(v, v))),
        s.mul(s).mul(norm_sq(v)),
    );
}

/// 0 ≤ norm_sq(v)
pub proof fn lemma_norm_sq_nonneg<T: OrderedRing>(v: Vec4<T>)
    ensures
        T::zero().le(norm_sq(v)),
{
    // 0 ≤ x²+y²+z²
    inequalities::lemma_sum_squares_nonneg_3d::<T>(v.x, v.y, v.z);
    // 0 ≤ w²
    ordered_ring_lemmas::lemma_square_nonneg::<T>(v.w);
    // 0 ≤ (x²+y²+z²) + w²
    inequalities::lemma_nonneg_add::<T>(
        v.x.mul(v.x).add(v.y.mul(v.y)).add(v.z.mul(v.z)),
        v.w.mul(v.w),
    );
}

/// norm_sq(v) ≡ 0 implies v ≡ zero (for OrderedField)
pub proof fn lemma_norm_sq_zero_implies_zero<T: OrderedField>(v: Vec4<T>)
    requires
        norm_sq(v).eqv(T::zero()),
    ensures
        v.eqv(Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: T::zero() }),
{
    // norm_sq(v) = (x²+y²+z²) + w², which ≡ 0
    // Both summands are non-negative
    let sum3 = v.x.mul(v.x).add(v.y.mul(v.y)).add(v.z.mul(v.z));
    let w2 = v.w.mul(v.w);
    inequalities::lemma_sum_squares_nonneg_3d::<T>(v.x, v.y, v.z);
    ordered_ring_lemmas::lemma_square_nonneg::<T>(v.w);

    // 0 ≤ sum3, 0 ≤ w2, sum3 + w2 ≡ 0
    // Need sum3 ≡ 0 and w2 ≡ 0
    // If sum3 ≢ 0, then 0 < sum3, so sum3 + w2 > 0, contradicting ≡ 0
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), sum3);
    T::axiom_eqv_symmetric(T::zero(), sum3);
    if !sum3.eqv(T::zero()) {
        ordered_ring_lemmas::lemma_add_pos_nonneg::<T>(sum3, w2);
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), sum3.add(w2));
        T::axiom_eqv_symmetric(T::zero(), sum3.add(w2));
    }
    // sum3 ≡ 0
    T::axiom_eqv_symmetric(sum3, T::zero());
    inequalities::lemma_sum_squares_zero_3d::<T>(v.x, v.y, v.z);

    // Similarly w² ≡ 0
    T::axiom_lt_iff_le_and_not_eqv(T::zero(), w2);
    T::axiom_eqv_symmetric(T::zero(), w2);
    if !w2.eqv(T::zero()) {
        ordered_ring_lemmas::lemma_add_nonneg_pos::<T>(sum3, w2);
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), sum3.add(w2));
        T::axiom_eqv_symmetric(T::zero(), sum3.add(w2));
    }
    // w² ≡ 0, so w ≡ 0
    T::axiom_eqv_symmetric(w2, T::zero());
    if !v.w.eqv(T::zero()) {
        verus_algebra::lemmas::field_lemmas::lemma_nonzero_product::<T>(v.w, v.w);
    }
}

/// v ≡ zero implies norm_sq(v) ≡ 0
pub proof fn lemma_norm_sq_zero_of_zero<T: Ring>(v: Vec4<T>)
    requires
        v.eqv(Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: T::zero() }),
    ensures
        norm_sq(v).eqv(T::zero()),
{
    let z = Vec4 { x: T::zero(), y: T::zero(), z: T::zero(), w: T::zero() };
    lemma_dot_congruence(v, z, v, z);
    lemma_dot_zero_right(z);
    T::axiom_eqv_transitive(norm_sq(v), dot(z, z), T::zero());
}

// ---------------------------------------------------------------------------
// Lerp
// ---------------------------------------------------------------------------

/// lerp(a, b, 0) ≡ a
pub proof fn lemma_lerp_zero<T: Ring>(a: Vec4<T>, b: Vec4<T>)
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

    // (1-0)*v.c ≡ v.c for each component
    T::axiom_mul_congruence_left(T::one().sub(T::zero()), T::one(), a.x);
    T::axiom_mul_congruence_left(T::one().sub(T::zero()), T::one(), a.y);
    T::axiom_mul_congruence_left(T::one().sub(T::zero()), T::one(), a.z);
    T::axiom_mul_congruence_left(T::one().sub(T::zero()), T::one(), a.w);
    ring_lemmas::lemma_mul_one_left::<T>(a.x);
    ring_lemmas::lemma_mul_one_left::<T>(a.y);
    ring_lemmas::lemma_mul_one_left::<T>(a.z);
    ring_lemmas::lemma_mul_one_left::<T>(a.w);
    T::axiom_eqv_transitive(T::one().sub(T::zero()).mul(a.x), T::one().mul(a.x), a.x);
    T::axiom_eqv_transitive(T::one().sub(T::zero()).mul(a.y), T::one().mul(a.y), a.y);
    T::axiom_eqv_transitive(T::one().sub(T::zero()).mul(a.z), T::one().mul(a.z), a.z);
    T::axiom_eqv_transitive(T::one().sub(T::zero()).mul(a.w), T::one().mul(a.w), a.w);

    // 0*b.c ≡ 0 for each component
    ring_lemmas::lemma_mul_zero_left::<T>(b.x);
    ring_lemmas::lemma_mul_zero_left::<T>(b.y);
    ring_lemmas::lemma_mul_zero_left::<T>(b.z);
    ring_lemmas::lemma_mul_zero_left::<T>(b.w);

    // (1-0)*a.c + 0*b.c ≡ a.c + 0
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().sub(T::zero()).mul(a.x), a.x, T::zero().mul(b.x), T::zero(),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().sub(T::zero()).mul(a.y), a.y, T::zero().mul(b.y), T::zero(),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().sub(T::zero()).mul(a.z), a.z, T::zero().mul(b.z), T::zero(),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().sub(T::zero()).mul(a.w), a.w, T::zero().mul(b.w), T::zero(),
    );

    // a.c + 0 ≡ a.c, chain
    T::axiom_add_zero_right(a.x);
    T::axiom_add_zero_right(a.y);
    T::axiom_add_zero_right(a.z);
    T::axiom_add_zero_right(a.w);
    T::axiom_eqv_transitive(
        T::one().sub(T::zero()).mul(a.x).add(T::zero().mul(b.x)), a.x.add(T::zero()), a.x,
    );
    T::axiom_eqv_transitive(
        T::one().sub(T::zero()).mul(a.y).add(T::zero().mul(b.y)), a.y.add(T::zero()), a.y,
    );
    T::axiom_eqv_transitive(
        T::one().sub(T::zero()).mul(a.z).add(T::zero().mul(b.z)), a.z.add(T::zero()), a.z,
    );
    T::axiom_eqv_transitive(
        T::one().sub(T::zero()).mul(a.w).add(T::zero().mul(b.w)), a.w.add(T::zero()), a.w,
    );
}

/// lerp(a, b, 1) ≡ b
pub proof fn lemma_lerp_one<T: Ring>(a: Vec4<T>, b: Vec4<T>)
    ensures
        lerp(a, b, T::one()).eqv(b),
{
    // 1 - 1 ≡ 0
    additive_group_lemmas::lemma_sub_self::<T>(T::one());

    // (1-1)*a.c ≡ 0
    T::axiom_mul_congruence_left(T::one().sub(T::one()), T::zero(), a.x);
    T::axiom_mul_congruence_left(T::one().sub(T::one()), T::zero(), a.y);
    T::axiom_mul_congruence_left(T::one().sub(T::one()), T::zero(), a.z);
    T::axiom_mul_congruence_left(T::one().sub(T::one()), T::zero(), a.w);
    ring_lemmas::lemma_mul_zero_left::<T>(a.x);
    ring_lemmas::lemma_mul_zero_left::<T>(a.y);
    ring_lemmas::lemma_mul_zero_left::<T>(a.z);
    ring_lemmas::lemma_mul_zero_left::<T>(a.w);
    T::axiom_eqv_transitive(T::one().sub(T::one()).mul(a.x), T::zero().mul(a.x), T::zero());
    T::axiom_eqv_transitive(T::one().sub(T::one()).mul(a.y), T::zero().mul(a.y), T::zero());
    T::axiom_eqv_transitive(T::one().sub(T::one()).mul(a.z), T::zero().mul(a.z), T::zero());
    T::axiom_eqv_transitive(T::one().sub(T::one()).mul(a.w), T::zero().mul(a.w), T::zero());

    // 1*b.c ≡ b.c
    ring_lemmas::lemma_mul_one_left::<T>(b.x);
    ring_lemmas::lemma_mul_one_left::<T>(b.y);
    ring_lemmas::lemma_mul_one_left::<T>(b.z);
    ring_lemmas::lemma_mul_one_left::<T>(b.w);

    // (1-1)*a.c + 1*b.c ≡ 0 + b.c
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().sub(T::one()).mul(a.x), T::zero(), T::one().mul(b.x), b.x,
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().sub(T::one()).mul(a.y), T::zero(), T::one().mul(b.y), b.y,
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().sub(T::one()).mul(a.z), T::zero(), T::one().mul(b.z), b.z,
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        T::one().sub(T::one()).mul(a.w), T::zero(), T::one().mul(b.w), b.w,
    );

    // 0 + b.c ≡ b.c, chain
    additive_group_lemmas::lemma_add_zero_left::<T>(b.x);
    additive_group_lemmas::lemma_add_zero_left::<T>(b.y);
    additive_group_lemmas::lemma_add_zero_left::<T>(b.z);
    additive_group_lemmas::lemma_add_zero_left::<T>(b.w);
    T::axiom_eqv_transitive(
        T::one().sub(T::one()).mul(a.x).add(T::one().mul(b.x)), T::zero().add(b.x), b.x,
    );
    T::axiom_eqv_transitive(
        T::one().sub(T::one()).mul(a.y).add(T::one().mul(b.y)), T::zero().add(b.y), b.y,
    );
    T::axiom_eqv_transitive(
        T::one().sub(T::one()).mul(a.z).add(T::one().mul(b.z)), T::zero().add(b.z), b.z,
    );
    T::axiom_eqv_transitive(
        T::one().sub(T::one()).mul(a.w).add(T::one().mul(b.w)), T::zero().add(b.w), b.w,
    );
}

/// lerp(a, a, t) ≡ a
pub proof fn lemma_lerp_self<T: Ring>(a: Vec4<T>, t: T)
    ensures
        lerp(a, a, t).eqv(a),
{
    // scale(1-t, a) + scale(t, a) ≡ scale((1-t)+t, a)
    lemma_scale_add_distributes(T::one().sub(t), t, a);
    Vec4::<T>::axiom_eqv_symmetric(
        scale(T::one().sub(t).add(t), a),
        scale(T::one().sub(t), a).add(scale(t, a)),
    );

    // (1-t)+t ≡ 1
    additive_group_lemmas::lemma_sub_then_add_cancel::<T>(T::one(), t);

    // scale((1-t)+t, a) ≡ scale(1, a) ≡ a
    T::axiom_mul_congruence_left(T::one().sub(t).add(t), T::one(), a.x);
    T::axiom_mul_congruence_left(T::one().sub(t).add(t), T::one(), a.y);
    T::axiom_mul_congruence_left(T::one().sub(t).add(t), T::one(), a.z);
    T::axiom_mul_congruence_left(T::one().sub(t).add(t), T::one(), a.w);
    ring_lemmas::lemma_mul_one_left::<T>(a.x);
    ring_lemmas::lemma_mul_one_left::<T>(a.y);
    ring_lemmas::lemma_mul_one_left::<T>(a.z);
    ring_lemmas::lemma_mul_one_left::<T>(a.w);
    T::axiom_eqv_transitive(T::one().sub(t).add(t).mul(a.x), T::one().mul(a.x), a.x);
    T::axiom_eqv_transitive(T::one().sub(t).add(t).mul(a.y), T::one().mul(a.y), a.y);
    T::axiom_eqv_transitive(T::one().sub(t).add(t).mul(a.z), T::one().mul(a.z), a.z);
    T::axiom_eqv_transitive(T::one().sub(t).add(t).mul(a.w), T::one().mul(a.w), a.w);

    // Chain: lerp(a, a, t) ≡ scale((1-t)+t, a) ≡ a
    Vec4::<T>::axiom_eqv_transitive(
        lerp(a, a, t),
        scale(T::one().sub(t).add(t), a),
        a,
    );
}

// ---------------------------------------------------------------------------
// Inner product identities
// ---------------------------------------------------------------------------

/// norm_sq(a+b) ≡ norm_sq(a) + 2·dot(a,b) + norm_sq(b)
proof fn lemma_norm_sq_add_expand<T: Ring>(a: Vec4<T>, b: Vec4<T>)
    ensures
        norm_sq(a.add(b)).eqv(
            norm_sq(a).add(two::<T>().mul(dot(a, b))).add(norm_sq(b))
        ),
{
    let na = norm_sq(a);
    let nb = norm_sq(b);
    let d = dot(a, b);

    lemma_dot_distributes_left(a, b, a.add(b));
    lemma_dot_distributes_right(a, a, b);
    lemma_dot_distributes_right(b, a, b);

    lemma_dot_commutative(b, a);
    T::axiom_eqv_reflexive(nb);
    additive_group_lemmas::lemma_add_congruence::<T>(
        dot(b, a), d, dot(b, b), nb,
    );
    T::axiom_eqv_transitive(
        dot(b, a.add(b)), dot(b, a).add(dot(b, b)), d.add(nb),
    );

    additive_group_lemmas::lemma_add_congruence::<T>(
        dot(a, a.add(b)), na.add(d),
        dot(b, a.add(b)), d.add(nb),
    );
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)),
        dot(a, a.add(b)).add(dot(b, a.add(b))),
        na.add(d).add(d.add(nb)),
    );

    T::axiom_add_associative(na.add(d), d, nb);
    T::axiom_eqv_symmetric(na.add(d).add(d).add(nb), na.add(d).add(d.add(nb)));
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)),
        na.add(d).add(d.add(nb)),
        na.add(d).add(d).add(nb),
    );

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
pub proof fn lemma_pythagorean<T: Ring>(a: Vec4<T>, b: Vec4<T>)
    requires
        dot(a, b).eqv(T::zero()),
    ensures
        norm_sq(a.add(b)).eqv(norm_sq(a).add(norm_sq(b))),
{
    let na = norm_sq(a);
    let nb = norm_sq(b);
    let d = dot(a, b);

    lemma_norm_sq_add_expand(a, b);

    ring_lemmas::lemma_mul_congruence_right::<T>(two::<T>(), d, T::zero());
    T::axiom_mul_zero_right(two::<T>());
    T::axiom_eqv_transitive(two::<T>().mul(d), two::<T>().mul(T::zero()), T::zero());

    additive_group_lemmas::lemma_add_congruence_right::<T>(na, two::<T>().mul(d), T::zero());
    T::axiom_add_zero_right(na);
    T::axiom_eqv_transitive(na.add(two::<T>().mul(d)), na.add(T::zero()), na);

    T::axiom_eqv_reflexive(nb);
    additive_group_lemmas::lemma_add_congruence::<T>(
        na.add(two::<T>().mul(d)), na, nb, nb,
    );

    T::axiom_eqv_transitive(
        norm_sq(a.add(b)),
        na.add(two::<T>().mul(d)).add(nb),
        na.add(nb),
    );
}

/// norm_sq(a-b) ≡ norm_sq(a) - 2·dot(a,b) + norm_sq(b)
proof fn lemma_norm_sq_sub_expand<T: Ring>(a: Vec4<T>, b: Vec4<T>)
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

    Vec4::<T>::axiom_sub_is_add_neg(a, b);
    lemma_norm_sq_congruence(a.sub(b), a.add(neg_b));

    lemma_norm_sq_add_expand(a, neg_b);
    T::axiom_eqv_transitive(
        norm_sq(a.sub(b)), norm_sq(a.add(neg_b)),
        na.add(t.mul(dot(a, neg_b))).add(norm_sq(neg_b)),
    );

    lemma_dot_neg_right(a, b);
    ring_lemmas::lemma_mul_congruence_right::<T>(t, dot(a, neg_b), d.neg());
    ring_lemmas::lemma_mul_neg_right::<T>(t, d);
    T::axiom_eqv_transitive(t.mul(dot(a, neg_b)), t.mul(d.neg()), t.mul(d).neg());

    lemma_dot_neg_right(neg_b, b);
    lemma_dot_commutative(neg_b, b);
    lemma_dot_neg_right(b, b);
    T::axiom_eqv_transitive(dot(neg_b, b), dot(b, neg_b), nb.neg());
    additive_group_lemmas::lemma_neg_congruence::<T>(dot(neg_b, b), nb.neg());
    T::axiom_eqv_transitive(norm_sq(neg_b), dot(neg_b, b).neg(), nb.neg().neg());
    additive_group_lemmas::lemma_neg_involution::<T>(nb);
    T::axiom_eqv_transitive(norm_sq(neg_b), nb.neg().neg(), nb);

    additive_group_lemmas::lemma_add_congruence_right::<T>(
        na, t.mul(dot(a, neg_b)), t.mul(d).neg(),
    );
    T::axiom_sub_is_add_neg(na, t.mul(d));
    T::axiom_eqv_symmetric(na.sub(t.mul(d)), na.add(t.mul(d).neg()));
    T::axiom_eqv_transitive(
        na.add(t.mul(dot(a, neg_b))), na.add(t.mul(d).neg()), na.sub(t.mul(d)),
    );

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
pub proof fn lemma_parallelogram<T: Ring>(a: Vec4<T>, b: Vec4<T>)
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

    additive_group_lemmas::lemma_add_congruence::<T>(
        norm_sq(a.add(b)), na.add(td).add(nb),
        norm_sq(a.sub(b)), na.sub(td).add(nb),
    );

    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        na.add(td), nb, na.sub(td), nb,
    );
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)).add(norm_sq(a.sub(b))),
        na.add(td).add(nb).add(na.sub(td).add(nb)),
        na.add(td).add(na.sub(td)).add(nb.add(nb)),
    );

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

    ring_lemmas::lemma_mul_two::<T>(na);
    ring_lemmas::lemma_mul_two::<T>(nb);

    T::axiom_eqv_reflexive(nb.add(nb));
    additive_group_lemmas::lemma_add_congruence::<T>(
        na.add(td).add(na.sub(td)), na.add(na), nb.add(nb), nb.add(nb),
    );
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)).add(norm_sq(a.sub(b))),
        na.add(td).add(na.sub(td)).add(nb.add(nb)),
        na.add(na).add(nb.add(nb)),
    );

    additive_group_lemmas::lemma_add_congruence::<T>(
        na.add(na), t.mul(na), nb.add(nb), t.mul(nb),
    );
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)).add(norm_sq(a.sub(b))),
        na.add(na).add(nb.add(nb)),
        t.mul(na).add(t.mul(nb)),
    );

    T::axiom_mul_distributes_left(t, na, nb);
    T::axiom_eqv_symmetric(t.mul(na.add(nb)), t.mul(na).add(t.mul(nb)));
    T::axiom_eqv_transitive(
        norm_sq(a.add(b)).add(norm_sq(a.sub(b))),
        t.mul(na).add(t.mul(nb)),
        t.mul(na.add(nb)),
    );
}

/// Polarization identity: 4·dot(a,b) ≡ norm_sq(a+b) - norm_sq(a-b)
pub proof fn lemma_polarization<T: Ring>(a: Vec4<T>, b: Vec4<T>)
    ensures
        two::<T>().mul(two::<T>()).mul(dot(a, b)).eqv(
            norm_sq(a.add(b)).sub(norm_sq(a.sub(b)))
        ),
{
    let na = norm_sq(a);
    let nb = norm_sq(b);
    let t = two::<T>();
    let td = t.mul(dot(a, b));

    T::axiom_mul_associative(t, t, dot(a, b));
    ring_lemmas::lemma_mul_two::<T>(td);
    T::axiom_eqv_symmetric(td.add(td), t.mul(td));
    T::axiom_eqv_transitive(t.mul(t).mul(dot(a, b)), t.mul(td), td.add(td));

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

    T::axiom_eqv_symmetric(
        norm_sq(a.add(b)).sub(norm_sq(a.sub(b))), td.add(td),
    );
    T::axiom_eqv_transitive(
        t.mul(t).mul(dot(a, b)), td.add(td),
        norm_sq(a.add(b)).sub(norm_sq(a.sub(b))),
    );
}

/// Cauchy-Schwarz inequality: dot(a,b)² ≤ norm_sq(a) · norm_sq(b)
pub proof fn lemma_cauchy_schwarz<T: OrderedRing>(a: Vec4<T>, b: Vec4<T>)
    ensures
        dot(a, b).mul(dot(a, b)).le(norm_sq(a).mul(norm_sq(b))),
{
    inequalities::lemma_cauchy_schwarz_4d::<T>(a.x, a.y, a.z, a.w, b.x, b.y, b.z, b.w);
}

// ---------------------------------------------------------------------------
// Componentwise min/max
// ---------------------------------------------------------------------------

pub open spec fn cwise_min<T: OrderedRing>(a: Vec4<T>, b: Vec4<T>) -> Vec4<T> {
    Vec4 {
        x: min_max::min(a.x, b.x),
        y: min_max::min(a.y, b.y),
        z: min_max::min(a.z, b.z),
        w: min_max::min(a.w, b.w),
    }
}

pub open spec fn cwise_max<T: OrderedRing>(a: Vec4<T>, b: Vec4<T>) -> Vec4<T> {
    Vec4 {
        x: min_max::max(a.x, b.x),
        y: min_max::max(a.y, b.y),
        z: min_max::max(a.z, b.z),
        w: min_max::max(a.w, b.w),
    }
}

/// Each component of cwise_min(a, b) ≤ corresponding component of a
pub proof fn lemma_cwise_min_le_left<T: OrderedRing>(a: Vec4<T>, b: Vec4<T>)
    ensures
        cwise_min(a, b).x.le(a.x),
        cwise_min(a, b).y.le(a.y),
        cwise_min(a, b).z.le(a.z),
        cwise_min(a, b).w.le(a.w),
{
    min_max::lemma_min_le_left::<T>(a.x, b.x);
    min_max::lemma_min_le_left::<T>(a.y, b.y);
    min_max::lemma_min_le_left::<T>(a.z, b.z);
    min_max::lemma_min_le_left::<T>(a.w, b.w);
}

/// Each component of cwise_min(a, b) ≤ corresponding component of b
pub proof fn lemma_cwise_min_le_right<T: OrderedRing>(a: Vec4<T>, b: Vec4<T>)
    ensures
        cwise_min(a, b).x.le(b.x),
        cwise_min(a, b).y.le(b.y),
        cwise_min(a, b).z.le(b.z),
        cwise_min(a, b).w.le(b.w),
{
    min_max::lemma_min_le_right::<T>(a.x, b.x);
    min_max::lemma_min_le_right::<T>(a.y, b.y);
    min_max::lemma_min_le_right::<T>(a.z, b.z);
    min_max::lemma_min_le_right::<T>(a.w, b.w);
}

/// Each component of a ≤ corresponding component of cwise_max(a, b)
pub proof fn lemma_cwise_max_ge_left<T: OrderedRing>(a: Vec4<T>, b: Vec4<T>)
    ensures
        a.x.le(cwise_max(a, b).x),
        a.y.le(cwise_max(a, b).y),
        a.z.le(cwise_max(a, b).z),
        a.w.le(cwise_max(a, b).w),
{
    min_max::lemma_max_ge_left::<T>(a.x, b.x);
    min_max::lemma_max_ge_left::<T>(a.y, b.y);
    min_max::lemma_max_ge_left::<T>(a.z, b.z);
    min_max::lemma_max_ge_left::<T>(a.w, b.w);
}

/// Each component of b ≤ corresponding component of cwise_max(a, b)
pub proof fn lemma_cwise_max_ge_right<T: OrderedRing>(a: Vec4<T>, b: Vec4<T>)
    ensures
        b.x.le(cwise_max(a, b).x),
        b.y.le(cwise_max(a, b).y),
        b.z.le(cwise_max(a, b).z),
        b.w.le(cwise_max(a, b).w),
{
    min_max::lemma_max_ge_right::<T>(a.x, b.x);
    min_max::lemma_max_ge_right::<T>(a.y, b.y);
    min_max::lemma_max_ge_right::<T>(a.z, b.z);
    min_max::lemma_max_ge_right::<T>(a.w, b.w);
}

} // verus!
