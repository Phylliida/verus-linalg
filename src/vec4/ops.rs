use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_commutative_monoid_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
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

} // verus!
