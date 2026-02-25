use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_commutative_monoid_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::inequalities;
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

} // verus!
