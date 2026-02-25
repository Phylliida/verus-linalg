use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_commutative_monoid_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use super::Vec3;

verus! {

// ---------------------------------------------------------------------------
// Spec functions
// ---------------------------------------------------------------------------

pub open spec fn scale<T: Ring>(s: T, v: Vec3<T>) -> Vec3<T> {
    Vec3 { x: s.mul(v.x), y: s.mul(v.y), z: s.mul(v.z) }
}

pub open spec fn dot<T: Ring>(a: Vec3<T>, b: Vec3<T>) -> T {
    a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z))
}

pub open spec fn cross<T: Ring>(a: Vec3<T>, b: Vec3<T>) -> Vec3<T> {
    Vec3 {
        x: a.y.mul(b.z).sub(a.z.mul(b.y)),
        y: a.z.mul(b.x).sub(a.x.mul(b.z)),
        z: a.x.mul(b.y).sub(a.y.mul(b.x)),
    }
}

// ---------------------------------------------------------------------------
// Scale lemmas
// ---------------------------------------------------------------------------

/// scale(s, a + b) ≡ scale(s, a) + scale(s, b)
pub proof fn lemma_scale_distributes_over_add<T: Ring>(s: T, a: Vec3<T>, b: Vec3<T>)
    ensures
        scale(s, a.add(b)).eqv(scale(s, a).add(scale(s, b))),
{
    T::axiom_mul_distributes_left(s, a.x, b.x);
    T::axiom_mul_distributes_left(s, a.y, b.y);
    T::axiom_mul_distributes_left(s, a.z, b.z);
}

/// scale(s + t, a) ≡ scale(s, a) + scale(t, a)
pub proof fn lemma_scale_add_distributes<T: Ring>(s: T, t: T, a: Vec3<T>)
    ensures
        scale(s.add(t), a).eqv(scale(s, a).add(scale(t, a))),
{
    ring_lemmas::lemma_mul_distributes_right::<T>(s, t, a.x);
    ring_lemmas::lemma_mul_distributes_right::<T>(s, t, a.y);
    ring_lemmas::lemma_mul_distributes_right::<T>(s, t, a.z);
}

/// scale(1, a) ≡ a
pub proof fn lemma_scale_identity<T: Ring>(a: Vec3<T>)
    ensures
        scale(T::one(), a).eqv(a),
{
    ring_lemmas::lemma_mul_one_left::<T>(a.x);
    ring_lemmas::lemma_mul_one_left::<T>(a.y);
    ring_lemmas::lemma_mul_one_left::<T>(a.z);
}

/// scale(0, a) ≡ zero
pub proof fn lemma_scale_zero_scalar<T: Ring>(a: Vec3<T>)
    ensures
        scale(T::zero(), a).eqv(Vec3 { x: T::zero(), y: T::zero(), z: T::zero() }),
{
    ring_lemmas::lemma_mul_zero_left::<T>(a.x);
    ring_lemmas::lemma_mul_zero_left::<T>(a.y);
    ring_lemmas::lemma_mul_zero_left::<T>(a.z);
}

/// scale(s, zero) ≡ zero
pub proof fn lemma_scale_zero_vec<T: Ring>(s: T)
    ensures
        scale(s, Vec3 { x: T::zero(), y: T::zero(), z: T::zero() })
            .eqv(Vec3 { x: T::zero(), y: T::zero(), z: T::zero() }),
{
    T::axiom_mul_zero_right(s);
}

/// a ≡ b implies scale(s, a) ≡ scale(s, b)
pub proof fn lemma_scale_congruence<T: Ring>(s: T, a: Vec3<T>, b: Vec3<T>)
    requires
        a.eqv(b),
    ensures
        scale(s, a).eqv(scale(s, b)),
{
    ring_lemmas::lemma_mul_congruence_right::<T>(s, a.x, b.x);
    ring_lemmas::lemma_mul_congruence_right::<T>(s, a.y, b.y);
    ring_lemmas::lemma_mul_congruence_right::<T>(s, a.z, b.z);
}

/// scale(s, scale(t, a)) ≡ scale(s * t, a)
pub proof fn lemma_scale_associative<T: Ring>(s: T, t: T, a: Vec3<T>)
    ensures
        scale(s, scale(t, a)).eqv(scale(s.mul(t), a)),
{
    T::axiom_mul_associative(s, t, a.x);
    T::axiom_eqv_symmetric(s.mul(t).mul(a.x), s.mul(t.mul(a.x)));
    T::axiom_mul_associative(s, t, a.y);
    T::axiom_eqv_symmetric(s.mul(t).mul(a.y), s.mul(t.mul(a.y)));
    T::axiom_mul_associative(s, t, a.z);
    T::axiom_eqv_symmetric(s.mul(t).mul(a.z), s.mul(t.mul(a.z)));
}

/// scale(-s, a) ≡ -scale(s, a)
pub proof fn lemma_scale_neg_scalar<T: Ring>(s: T, a: Vec3<T>)
    ensures
        scale(s.neg(), a).eqv(scale(s, a).neg()),
{
    ring_lemmas::lemma_mul_neg_left::<T>(s, a.x);
    ring_lemmas::lemma_mul_neg_left::<T>(s, a.y);
    ring_lemmas::lemma_mul_neg_left::<T>(s, a.z);
}

/// scale(s, -a) ≡ -scale(s, a)
pub proof fn lemma_scale_neg_vec<T: Ring>(s: T, a: Vec3<T>)
    ensures
        scale(s, a.neg()).eqv(scale(s, a).neg()),
{
    ring_lemmas::lemma_mul_neg_right::<T>(s, a.x);
    ring_lemmas::lemma_mul_neg_right::<T>(s, a.y);
    ring_lemmas::lemma_mul_neg_right::<T>(s, a.z);
}

/// scale(s, a - b) ≡ scale(s, a) - scale(s, b)
pub proof fn lemma_scale_sub_distributes<T: Ring>(s: T, a: Vec3<T>, b: Vec3<T>)
    ensures
        scale(s, a.sub(b)).eqv(scale(s, a).sub(scale(s, b))),
{
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.x, b.x);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.y, b.y);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.z, b.z);
}

// ---------------------------------------------------------------------------
// Dot lemmas
// ---------------------------------------------------------------------------

/// dot(a, b) ≡ dot(b, a)
pub proof fn lemma_dot_commutative<T: Ring>(a: Vec3<T>, b: Vec3<T>)
    ensures
        dot(a, b).eqv(dot(b, a)),
{
    T::axiom_mul_commutative(a.x, b.x);
    T::axiom_mul_commutative(a.y, b.y);
    T::axiom_mul_commutative(a.z, b.z);
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
}

/// dot(a, zero) ≡ 0
pub proof fn lemma_dot_zero_right<T: Ring>(a: Vec3<T>)
    ensures
        dot(a, Vec3 { x: T::zero(), y: T::zero(), z: T::zero() }).eqv(T::zero()),
{
    T::axiom_mul_zero_right(a.x);
    T::axiom_mul_zero_right(a.y);
    T::axiom_mul_zero_right(a.z);
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
}

/// dot(zero, a) ≡ 0
pub proof fn lemma_dot_zero_left<T: Ring>(a: Vec3<T>)
    ensures
        dot(Vec3 { x: T::zero(), y: T::zero(), z: T::zero() }, a).eqv(T::zero()),
{
    ring_lemmas::lemma_mul_zero_left::<T>(a.x);
    ring_lemmas::lemma_mul_zero_left::<T>(a.y);
    ring_lemmas::lemma_mul_zero_left::<T>(a.z);
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
}

/// dot(a, b + c) ≡ dot(a, b) + dot(a, c)
pub proof fn lemma_dot_distributes_right<T: Ring>(a: Vec3<T>, b: Vec3<T>, c: Vec3<T>)
    ensures
        dot(a, b.add(c)).eqv(dot(a, b).add(dot(a, c))),
{
    // Distribute each component
    T::axiom_mul_distributes_left(a.x, b.x, c.x);
    T::axiom_mul_distributes_left(a.y, b.y, c.y);
    T::axiom_mul_distributes_left(a.z, b.z, c.z);

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
    // LHS ≡ ((axbx+axcx)+(ayby+aycy))+(azbz+azcz)

    // Rearrange inner: (axbx+axcx)+(ayby+aycy) ≡ (axbx+ayby)+(axcx+aycy)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.x.mul(b.x), a.x.mul(c.x), a.y.mul(b.y), a.y.mul(c.y),
    );
    // Propagate through z add
    T::axiom_add_congruence_left(
        a.x.mul(b.x).add(a.x.mul(c.x)).add(a.y.mul(b.y).add(a.y.mul(c.y))),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.x.mul(c.x).add(a.y.mul(c.y))),
        a.z.mul(b.z).add(a.z.mul(c.z)),
    );

    // Rearrange outer: ((axbx+ayby)+(axcx+aycy))+(azbz+azcz)
    //   ≡ ((axbx+ayby)+azbz)+((axcx+aycy)+azcz)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.x.mul(b.x).add(a.y.mul(b.y)),
        a.x.mul(c.x).add(a.y.mul(c.y)),
        a.z.mul(b.z),
        a.z.mul(c.z),
    );

    // Chain: LHS ≡ E1 ≡ E2 ≡ RHS
    T::axiom_eqv_transitive(
        dot(a, b.add(c)),
        a.x.mul(b.x).add(a.x.mul(c.x)).add(a.y.mul(b.y).add(a.y.mul(c.y))).add(a.z.mul(b.z).add(a.z.mul(c.z))),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.x.mul(c.x).add(a.y.mul(c.y))).add(a.z.mul(b.z).add(a.z.mul(c.z))),
    );
    T::axiom_eqv_transitive(
        dot(a, b.add(c)),
        a.x.mul(b.x).add(a.y.mul(b.y)).add(a.x.mul(c.x).add(a.y.mul(c.y))).add(a.z.mul(b.z).add(a.z.mul(c.z))),
        dot(a, b).add(dot(a, c)),
    );
}

/// dot(a + b, c) ≡ dot(a, c) + dot(b, c)
pub proof fn lemma_dot_distributes_left<T: Ring>(a: Vec3<T>, b: Vec3<T>, c: Vec3<T>)
    ensures
        dot(a.add(b), c).eqv(dot(a, c).add(dot(b, c))),
{
    // Distribute each component
    ring_lemmas::lemma_mul_distributes_right::<T>(a.x, b.x, c.x);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.y, b.y, c.y);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.z, b.z, c.z);

    // Propagate first two
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.add(b.x).mul(c.x), a.x.mul(c.x).add(b.x.mul(c.x)),
        a.y.add(b.y).mul(c.y), a.y.mul(c.y).add(b.y.mul(c.y)),
    );
    // Propagate with third
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.x.add(b.x).mul(c.x).add(a.y.add(b.y).mul(c.y)),
        a.x.mul(c.x).add(b.x.mul(c.x)).add(a.y.mul(c.y).add(b.y.mul(c.y))),
        a.z.add(b.z).mul(c.z),
        a.z.mul(c.z).add(b.z.mul(c.z)),
    );

    // Rearrange inner
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.x.mul(c.x), b.x.mul(c.x), a.y.mul(c.y), b.y.mul(c.y),
    );
    T::axiom_add_congruence_left(
        a.x.mul(c.x).add(b.x.mul(c.x)).add(a.y.mul(c.y).add(b.y.mul(c.y))),
        a.x.mul(c.x).add(a.y.mul(c.y)).add(b.x.mul(c.x).add(b.y.mul(c.y))),
        a.z.mul(c.z).add(b.z.mul(c.z)),
    );

    // Rearrange outer
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        a.x.mul(c.x).add(a.y.mul(c.y)),
        b.x.mul(c.x).add(b.y.mul(c.y)),
        a.z.mul(c.z),
        b.z.mul(c.z),
    );

    // Chain
    T::axiom_eqv_transitive(
        dot(a.add(b), c),
        a.x.mul(c.x).add(b.x.mul(c.x)).add(a.y.mul(c.y).add(b.y.mul(c.y))).add(a.z.mul(c.z).add(b.z.mul(c.z))),
        a.x.mul(c.x).add(a.y.mul(c.y)).add(b.x.mul(c.x).add(b.y.mul(c.y))).add(a.z.mul(c.z).add(b.z.mul(c.z))),
    );
    T::axiom_eqv_transitive(
        dot(a.add(b), c),
        a.x.mul(c.x).add(a.y.mul(c.y)).add(b.x.mul(c.x).add(b.y.mul(c.y))).add(a.z.mul(c.z).add(b.z.mul(c.z))),
        dot(a, c).add(dot(b, c)),
    );
}

/// dot(scale(s, a), b) ≡ s * dot(a, b)
pub proof fn lemma_dot_scale_left<T: Ring>(s: T, a: Vec3<T>, b: Vec3<T>)
    ensures
        dot(scale(s, a), b).eqv(s.mul(dot(a, b))),
{
    // (s*ai)*bi ≡ s*(ai*bi)
    T::axiom_mul_associative(s, a.x, b.x);
    T::axiom_mul_associative(s, a.y, b.y);
    T::axiom_mul_associative(s, a.z, b.z);

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
    // LHS ≡ s*(ax*bx) + s*(ay*by) + s*(az*bz)

    // Factor inner: s*(ax*bx) + s*(ay*by) ≡ s*(ax*bx + ay*by)
    T::axiom_mul_distributes_left(s, a.x.mul(b.x), a.y.mul(b.y));
    T::axiom_eqv_symmetric(
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y))),
        s.mul(a.x.mul(b.x)).add(s.mul(a.y.mul(b.y))),
    );
    // Propagate: (s*(ax*bx) + s*(ay*by)) + s*(az*bz) ≡ s*(ax*bx + ay*by) + s*(az*bz)
    T::axiom_add_congruence_left(
        s.mul(a.x.mul(b.x)).add(s.mul(a.y.mul(b.y))),
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y))),
        s.mul(a.z.mul(b.z)),
    );

    // Factor outer: s*(ax*bx + ay*by) + s*(az*bz) ≡ s*((ax*bx + ay*by) + az*bz)
    T::axiom_mul_distributes_left(s, a.x.mul(b.x).add(a.y.mul(b.y)), a.z.mul(b.z));
    T::axiom_eqv_symmetric(
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y)).add(a.z.mul(b.z))),
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y))).add(s.mul(a.z.mul(b.z))),
    );

    // Chain: LHS ≡ E1 ≡ E2 ≡ RHS
    T::axiom_eqv_transitive(
        dot(scale(s, a), b),
        s.mul(a.x.mul(b.x)).add(s.mul(a.y.mul(b.y))).add(s.mul(a.z.mul(b.z))),
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y))).add(s.mul(a.z.mul(b.z))),
    );
    T::axiom_eqv_transitive(
        dot(scale(s, a), b),
        s.mul(a.x.mul(b.x).add(a.y.mul(b.y))).add(s.mul(a.z.mul(b.z))),
        s.mul(dot(a, b)),
    );
}

/// dot(a, scale(s, b)) ≡ s * dot(a, b)
pub proof fn lemma_dot_scale_right<T: Ring>(s: T, a: Vec3<T>, b: Vec3<T>)
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
// Cross lemmas
// ---------------------------------------------------------------------------

/// cross(a, b) ≡ -cross(b, a)
pub proof fn lemma_cross_anticommutative<T: Ring>(a: Vec3<T>, b: Vec3<T>)
    ensures
        cross(a, b).eqv(cross(b, a).neg()),
{
    // x component: a.y*b.z - a.z*b.y ≡ -(b.y*a.z - b.z*a.y)
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a.y.mul(b.z), a.z.mul(b.y));
    T::axiom_mul_commutative(a.z, b.y);
    T::axiom_mul_commutative(a.y, b.z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.z.mul(b.y), b.y.mul(a.z),
        a.y.mul(b.z), b.z.mul(a.y),
    );
    T::axiom_neg_congruence(
        a.z.mul(b.y).sub(a.y.mul(b.z)),
        b.y.mul(a.z).sub(b.z.mul(a.y)),
    );
    T::axiom_eqv_transitive(
        a.y.mul(b.z).sub(a.z.mul(b.y)),
        a.z.mul(b.y).sub(a.y.mul(b.z)).neg(),
        b.y.mul(a.z).sub(b.z.mul(a.y)).neg(),
    );

    // y component: a.z*b.x - a.x*b.z ≡ -(b.z*a.x - b.x*a.z)
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a.z.mul(b.x), a.x.mul(b.z));
    T::axiom_mul_commutative(a.x, b.z);
    T::axiom_mul_commutative(a.z, b.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.x.mul(b.z), b.z.mul(a.x),
        a.z.mul(b.x), b.x.mul(a.z),
    );
    T::axiom_neg_congruence(
        a.x.mul(b.z).sub(a.z.mul(b.x)),
        b.z.mul(a.x).sub(b.x.mul(a.z)),
    );
    T::axiom_eqv_transitive(
        a.z.mul(b.x).sub(a.x.mul(b.z)),
        a.x.mul(b.z).sub(a.z.mul(b.x)).neg(),
        b.z.mul(a.x).sub(b.x.mul(a.z)).neg(),
    );

    // z component: a.x*b.y - a.y*b.x ≡ -(b.x*a.y - b.y*a.x)
    additive_group_lemmas::lemma_sub_antisymmetric::<T>(a.x.mul(b.y), a.y.mul(b.x));
    T::axiom_mul_commutative(a.y, b.x);
    T::axiom_mul_commutative(a.x, b.y);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.y.mul(b.x), b.x.mul(a.y),
        a.x.mul(b.y), b.y.mul(a.x),
    );
    T::axiom_neg_congruence(
        a.y.mul(b.x).sub(a.x.mul(b.y)),
        b.x.mul(a.y).sub(b.y.mul(a.x)),
    );
    T::axiom_eqv_transitive(
        a.x.mul(b.y).sub(a.y.mul(b.x)),
        a.y.mul(b.x).sub(a.x.mul(b.y)).neg(),
        b.x.mul(a.y).sub(b.y.mul(a.x)).neg(),
    );
}

/// cross(a, a) ≡ zero
pub proof fn lemma_cross_self_zero<T: Ring>(a: Vec3<T>)
    ensures
        cross(a, a).eqv(Vec3 { x: T::zero(), y: T::zero(), z: T::zero() }),
{
    // x: a.y*a.z - a.z*a.y ≡ 0
    T::axiom_mul_commutative(a.y, a.z);
    additive_group_lemmas::lemma_eqv_implies_sub_eqv_zero::<T>(a.y.mul(a.z), a.z.mul(a.y));
    // y: a.z*a.x - a.x*a.z ≡ 0
    T::axiom_mul_commutative(a.z, a.x);
    additive_group_lemmas::lemma_eqv_implies_sub_eqv_zero::<T>(a.z.mul(a.x), a.x.mul(a.z));
    // z: a.x*a.y - a.y*a.x ≡ 0
    T::axiom_mul_commutative(a.x, a.y);
    additive_group_lemmas::lemma_eqv_implies_sub_eqv_zero::<T>(a.x.mul(a.y), a.y.mul(a.x));
}

// ---------------------------------------------------------------------------
// Helper: (a + b) - (c + d) ≡ (a - c) + (b - d)
// ---------------------------------------------------------------------------

proof fn lemma_sub_sum_distributes<T: Ring>(a: T, b: T, c: T, d: T)
    ensures
        a.add(b).sub(c.add(d)).eqv(a.sub(c).add(b.sub(d))),
{
    // (a+b) - (c+d) ≡ (a+b) + (-(c+d))
    T::axiom_sub_is_add_neg(a.add(b), c.add(d));
    // -(c+d) ≡ -c + -d
    additive_group_lemmas::lemma_neg_add::<T>(c, d);
    // (a+b) + (-(c+d)) ≡ (a+b) + (-c + -d)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.add(b), c.add(d).neg(), c.neg().add(d.neg()),
    );
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(b).add(c.add(d).neg()),
        a.add(b).add(c.neg().add(d.neg())),
    );
    // (a+b) + (-c + -d) ≡ (a + -c) + (b + -d)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a, b, c.neg(), d.neg());
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(b).add(c.neg().add(d.neg())),
        a.add(c.neg()).add(b.add(d.neg())),
    );
    // (a + -c) ≡ a - c
    T::axiom_sub_is_add_neg(a, c);
    T::axiom_eqv_symmetric(a.sub(c), a.add(c.neg()));
    // (b + -d) ≡ b - d
    T::axiom_sub_is_add_neg(b, d);
    T::axiom_eqv_symmetric(b.sub(d), b.add(d.neg()));
    // (a + -c) + (b + -d) ≡ (a - c) + (b - d)
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(c.neg()), a.sub(c),
        b.add(d.neg()), b.sub(d),
    );
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(c.neg()).add(b.add(d.neg())),
        a.sub(c).add(b.sub(d)),
    );
}

// ---------------------------------------------------------------------------
// Cross linearity lemmas
// ---------------------------------------------------------------------------

/// cross(a, b + c) ≡ cross(a, b) + cross(a, c)
pub proof fn lemma_cross_distributes_right<T: Ring>(a: Vec3<T>, b: Vec3<T>, c: Vec3<T>)
    ensures
        cross(a, b.add(c)).eqv(cross(a, b).add(cross(a, c))),
{
    // x component: a.y*(b.z+c.z) - a.z*(b.y+c.y) ≡ (a.y*b.z - a.z*b.y) + (a.y*c.z - a.z*c.y)
    T::axiom_mul_distributes_left(a.y, b.z, c.z);
    T::axiom_mul_distributes_left(a.z, b.y, c.y);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.y.mul(b.z.add(c.z)), a.y.mul(b.z).add(a.y.mul(c.z)),
        a.z.mul(b.y.add(c.y)), a.z.mul(b.y).add(a.z.mul(c.y)),
    );
    lemma_sub_sum_distributes::<T>(a.y.mul(b.z), a.y.mul(c.z), a.z.mul(b.y), a.z.mul(c.y));
    T::axiom_eqv_transitive(
        a.y.mul(b.z.add(c.z)).sub(a.z.mul(b.y.add(c.y))),
        a.y.mul(b.z).add(a.y.mul(c.z)).sub(a.z.mul(b.y).add(a.z.mul(c.y))),
        a.y.mul(b.z).sub(a.z.mul(b.y)).add(a.y.mul(c.z).sub(a.z.mul(c.y))),
    );

    // y component: a.z*(b.x+c.x) - a.x*(b.z+c.z) ≡ (a.z*b.x - a.x*b.z) + (a.z*c.x - a.x*c.z)
    T::axiom_mul_distributes_left(a.z, b.x, c.x);
    T::axiom_mul_distributes_left(a.x, b.z, c.z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.z.mul(b.x.add(c.x)), a.z.mul(b.x).add(a.z.mul(c.x)),
        a.x.mul(b.z.add(c.z)), a.x.mul(b.z).add(a.x.mul(c.z)),
    );
    lemma_sub_sum_distributes::<T>(a.z.mul(b.x), a.z.mul(c.x), a.x.mul(b.z), a.x.mul(c.z));
    T::axiom_eqv_transitive(
        a.z.mul(b.x.add(c.x)).sub(a.x.mul(b.z.add(c.z))),
        a.z.mul(b.x).add(a.z.mul(c.x)).sub(a.x.mul(b.z).add(a.x.mul(c.z))),
        a.z.mul(b.x).sub(a.x.mul(b.z)).add(a.z.mul(c.x).sub(a.x.mul(c.z))),
    );

    // z component: a.x*(b.y+c.y) - a.y*(b.x+c.x) ≡ (a.x*b.y - a.y*b.x) + (a.x*c.y - a.y*c.x)
    T::axiom_mul_distributes_left(a.x, b.y, c.y);
    T::axiom_mul_distributes_left(a.y, b.x, c.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.x.mul(b.y.add(c.y)), a.x.mul(b.y).add(a.x.mul(c.y)),
        a.y.mul(b.x.add(c.x)), a.y.mul(b.x).add(a.y.mul(c.x)),
    );
    lemma_sub_sum_distributes::<T>(a.x.mul(b.y), a.x.mul(c.y), a.y.mul(b.x), a.y.mul(c.x));
    T::axiom_eqv_transitive(
        a.x.mul(b.y.add(c.y)).sub(a.y.mul(b.x.add(c.x))),
        a.x.mul(b.y).add(a.x.mul(c.y)).sub(a.y.mul(b.x).add(a.y.mul(c.x))),
        a.x.mul(b.y).sub(a.y.mul(b.x)).add(a.x.mul(c.y).sub(a.y.mul(c.x))),
    );
}

/// cross(a + b, c) ≡ cross(a, c) + cross(b, c)
pub proof fn lemma_cross_distributes_left<T: Ring>(a: Vec3<T>, b: Vec3<T>, c: Vec3<T>)
    ensures
        cross(a.add(b), c).eqv(cross(a, c).add(cross(b, c))),
{
    // x component: (a.y+b.y)*c.z - (a.z+b.z)*c.y ≡ (a.y*c.z - a.z*c.y) + (b.y*c.z - b.z*c.y)
    ring_lemmas::lemma_mul_distributes_right::<T>(a.y, b.y, c.z);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.z, b.z, c.y);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.y.add(b.y).mul(c.z), a.y.mul(c.z).add(b.y.mul(c.z)),
        a.z.add(b.z).mul(c.y), a.z.mul(c.y).add(b.z.mul(c.y)),
    );
    lemma_sub_sum_distributes::<T>(a.y.mul(c.z), b.y.mul(c.z), a.z.mul(c.y), b.z.mul(c.y));
    T::axiom_eqv_transitive(
        a.y.add(b.y).mul(c.z).sub(a.z.add(b.z).mul(c.y)),
        a.y.mul(c.z).add(b.y.mul(c.z)).sub(a.z.mul(c.y).add(b.z.mul(c.y))),
        a.y.mul(c.z).sub(a.z.mul(c.y)).add(b.y.mul(c.z).sub(b.z.mul(c.y))),
    );

    // y component: (a.z+b.z)*c.x - (a.x+b.x)*c.z ≡ (a.z*c.x - a.x*c.z) + (b.z*c.x - b.x*c.z)
    ring_lemmas::lemma_mul_distributes_right::<T>(a.z, b.z, c.x);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.x, b.x, c.z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.z.add(b.z).mul(c.x), a.z.mul(c.x).add(b.z.mul(c.x)),
        a.x.add(b.x).mul(c.z), a.x.mul(c.z).add(b.x.mul(c.z)),
    );
    lemma_sub_sum_distributes::<T>(a.z.mul(c.x), b.z.mul(c.x), a.x.mul(c.z), b.x.mul(c.z));
    T::axiom_eqv_transitive(
        a.z.add(b.z).mul(c.x).sub(a.x.add(b.x).mul(c.z)),
        a.z.mul(c.x).add(b.z.mul(c.x)).sub(a.x.mul(c.z).add(b.x.mul(c.z))),
        a.z.mul(c.x).sub(a.x.mul(c.z)).add(b.z.mul(c.x).sub(b.x.mul(c.z))),
    );

    // z component: (a.x+b.x)*c.y - (a.y+b.y)*c.x ≡ (a.x*c.y - a.y*c.x) + (b.x*c.y - b.y*c.x)
    ring_lemmas::lemma_mul_distributes_right::<T>(a.x, b.x, c.y);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.y, b.y, c.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.x.add(b.x).mul(c.y), a.x.mul(c.y).add(b.x.mul(c.y)),
        a.y.add(b.y).mul(c.x), a.y.mul(c.x).add(b.y.mul(c.x)),
    );
    lemma_sub_sum_distributes::<T>(a.x.mul(c.y), b.x.mul(c.y), a.y.mul(c.x), b.y.mul(c.x));
    T::axiom_eqv_transitive(
        a.x.add(b.x).mul(c.y).sub(a.y.add(b.y).mul(c.x)),
        a.x.mul(c.y).add(b.x.mul(c.y)).sub(a.y.mul(c.x).add(b.y.mul(c.x))),
        a.x.mul(c.y).sub(a.y.mul(c.x)).add(b.x.mul(c.y).sub(b.y.mul(c.x))),
    );
}

/// cross(scale(s, a), b) ≡ scale(s, cross(a, b))
pub proof fn lemma_cross_scale<T: Ring>(s: T, a: Vec3<T>, b: Vec3<T>)
    ensures
        cross(scale(s, a), b).eqv(scale(s, cross(a, b))),
{
    // x: (s*a.y)*b.z - (s*a.z)*b.y ≡ s*(a.y*b.z - a.z*b.y)
    T::axiom_mul_associative(s, a.y, b.z);
    T::axiom_mul_associative(s, a.z, b.y);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(a.y).mul(b.z), s.mul(a.y.mul(b.z)),
        s.mul(a.z).mul(b.y), s.mul(a.z.mul(b.y)),
    );
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.y.mul(b.z), a.z.mul(b.y));
    T::axiom_eqv_symmetric(
        s.mul(a.y.mul(b.z).sub(a.z.mul(b.y))),
        s.mul(a.y.mul(b.z)).sub(s.mul(a.z.mul(b.y))),
    );
    T::axiom_eqv_transitive(
        s.mul(a.y).mul(b.z).sub(s.mul(a.z).mul(b.y)),
        s.mul(a.y.mul(b.z)).sub(s.mul(a.z.mul(b.y))),
        s.mul(a.y.mul(b.z).sub(a.z.mul(b.y))),
    );

    // y: (s*a.z)*b.x - (s*a.x)*b.z ≡ s*(a.z*b.x - a.x*b.z)
    T::axiom_mul_associative(s, a.z, b.x);
    T::axiom_mul_associative(s, a.x, b.z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(a.z).mul(b.x), s.mul(a.z.mul(b.x)),
        s.mul(a.x).mul(b.z), s.mul(a.x.mul(b.z)),
    );
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.z.mul(b.x), a.x.mul(b.z));
    T::axiom_eqv_symmetric(
        s.mul(a.z.mul(b.x).sub(a.x.mul(b.z))),
        s.mul(a.z.mul(b.x)).sub(s.mul(a.x.mul(b.z))),
    );
    T::axiom_eqv_transitive(
        s.mul(a.z).mul(b.x).sub(s.mul(a.x).mul(b.z)),
        s.mul(a.z.mul(b.x)).sub(s.mul(a.x.mul(b.z))),
        s.mul(a.z.mul(b.x).sub(a.x.mul(b.z))),
    );

    // z: (s*a.x)*b.y - (s*a.y)*b.x ≡ s*(a.x*b.y - a.y*b.x)
    T::axiom_mul_associative(s, a.x, b.y);
    T::axiom_mul_associative(s, a.y, b.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(a.x).mul(b.y), s.mul(a.x.mul(b.y)),
        s.mul(a.y).mul(b.x), s.mul(a.y.mul(b.x)),
    );
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.x.mul(b.y), a.y.mul(b.x));
    T::axiom_eqv_symmetric(
        s.mul(a.x.mul(b.y).sub(a.y.mul(b.x))),
        s.mul(a.x.mul(b.y)).sub(s.mul(a.y.mul(b.x))),
    );
    T::axiom_eqv_transitive(
        s.mul(a.x).mul(b.y).sub(s.mul(a.y).mul(b.x)),
        s.mul(a.x.mul(b.y)).sub(s.mul(a.y.mul(b.x))),
        s.mul(a.x.mul(b.y).sub(a.y.mul(b.x))),
    );
}

// ---------------------------------------------------------------------------
// Helper: (a * b) * c ≡ (a * c) * b (swap last two factors)
// ---------------------------------------------------------------------------

proof fn lemma_mul_right_swap<T: Ring>(a: T, b: T, c: T)
    ensures
        a.mul(b).mul(c).eqv(a.mul(c).mul(b)),
{
    // (a*b)*c ≡ a*(b*c)
    T::axiom_mul_associative(a, b, c);
    // b*c ≡ c*b
    T::axiom_mul_commutative(b, c);
    // a*(b*c) ≡ a*(c*b)
    ring_lemmas::lemma_mul_congruence_right::<T>(a, b.mul(c), c.mul(b));
    T::axiom_eqv_transitive(
        a.mul(b).mul(c),
        a.mul(b.mul(c)),
        a.mul(c.mul(b)),
    );
    // a*(c*b) ≡ (a*c)*b
    T::axiom_mul_associative(a, c, b);
    T::axiom_eqv_symmetric(a.mul(c).mul(b), a.mul(c.mul(b)));
    T::axiom_eqv_transitive(
        a.mul(b).mul(c),
        a.mul(c.mul(b)),
        a.mul(c).mul(b),
    );
}

// ---------------------------------------------------------------------------
// Cross orthogonality lemmas
// ---------------------------------------------------------------------------

/// dot(cross(a, b), a) ≡ 0
pub proof fn lemma_cross_orthogonal_left<T: Ring>(a: Vec3<T>, b: Vec3<T>)
    ensures
        dot(cross(a, b), a).eqv(T::zero()),
{
    // dot(cross(a,b), a) = (ay*bz - az*by)*ax + (az*bx - ax*bz)*ay + (ax*by - ay*bx)*az
    //
    // After expanding with sub_mul_right:
    // = (ay*bz*ax - az*by*ax) + (az*bx*ay - ax*bz*ay) + (ax*by*az - ay*bx*az)
    //
    // The 6 terms cancel pairwise:
    //   ay*bz*ax ≡ ax*bz*ay  (via right_swap: both ≡ (a_*a_)*b_)
    //   az*bx*ay ≡ ay*bx*az
    //   ax*by*az ≡ az*by*ax
    //
    // So we get: (T1+ - T1-) + (T2+ - T2-) + (T3+ - T3-)
    // where T1+ ≡ T2-, T2+ ≡ T3-, T3+ ≡ T1-.
    // After substitution: (q2-q1) + (q3-q2) + (q1-q3) which telescopes to 0.

    // Step 1: Expand each cross component times a_i using sub_mul_right
    ring_lemmas::lemma_sub_mul_right::<T>(a.y.mul(b.z), a.z.mul(b.y), a.x);
    ring_lemmas::lemma_sub_mul_right::<T>(a.z.mul(b.x), a.x.mul(b.z), a.y);
    ring_lemmas::lemma_sub_mul_right::<T>(a.x.mul(b.y), a.y.mul(b.x), a.z);

    // Step 2: Propagate through additions
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.y.mul(b.z).sub(a.z.mul(b.y)).mul(a.x),
        a.y.mul(b.z).mul(a.x).sub(a.z.mul(b.y).mul(a.x)),
        a.z.mul(b.x).sub(a.x.mul(b.z)).mul(a.y),
        a.z.mul(b.x).mul(a.y).sub(a.x.mul(b.z).mul(a.y)),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.y.mul(b.z).sub(a.z.mul(b.y)).mul(a.x).add(a.z.mul(b.x).sub(a.x.mul(b.z)).mul(a.y)),
        a.y.mul(b.z).mul(a.x).sub(a.z.mul(b.y).mul(a.x)).add(a.z.mul(b.x).mul(a.y).sub(a.x.mul(b.z).mul(a.y))),
        a.x.mul(b.y).sub(a.y.mul(b.x)).mul(a.z),
        a.x.mul(b.y).mul(a.z).sub(a.y.mul(b.x).mul(a.z)),
    );
    // dot(cross(a,b), a) ≡ (T1+-T1-) + (T2+-T2-) + (T3+-T3-)

    // Step 3: Show the pairwise equivalences using lemma_mul_right_swap
    // T1+ = ay*bz*ax, T2- = ax*bz*ay: both ≡ (a_*a_)*b_ form
    // (ay*bz)*ax ≡ (ay*ax)*bz
    lemma_mul_right_swap::<T>(a.y, b.z, a.x);
    // (ax*bz)*ay ≡ (ax*ay)*bz
    lemma_mul_right_swap::<T>(a.x, b.z, a.y);
    // (ay*ax) ≡ (ax*ay)
    T::axiom_mul_commutative(a.y, a.x);
    T::axiom_mul_congruence_left(a.y.mul(a.x), a.x.mul(a.y), b.z);
    // T1+ ≡ (ay*ax)*bz ≡ (ax*ay)*bz ≡ T2-
    T::axiom_eqv_transitive(
        a.y.mul(b.z).mul(a.x),
        a.y.mul(a.x).mul(b.z),
        a.x.mul(a.y).mul(b.z),
    );
    T::axiom_eqv_symmetric(a.x.mul(b.z).mul(a.y), a.x.mul(a.y).mul(b.z));
    T::axiom_eqv_transitive(
        a.y.mul(b.z).mul(a.x),
        a.x.mul(a.y).mul(b.z),
        a.x.mul(b.z).mul(a.y),
    );

    // T2+ = az*bx*ay, T3- = ay*bx*az: both ≡ (a_*a_)*b_
    lemma_mul_right_swap::<T>(a.z, b.x, a.y);
    lemma_mul_right_swap::<T>(a.y, b.x, a.z);
    T::axiom_mul_commutative(a.z, a.y);
    T::axiom_mul_congruence_left(a.z.mul(a.y), a.y.mul(a.z), b.x);
    T::axiom_eqv_transitive(
        a.z.mul(b.x).mul(a.y),
        a.z.mul(a.y).mul(b.x),
        a.y.mul(a.z).mul(b.x),
    );
    T::axiom_eqv_symmetric(a.y.mul(b.x).mul(a.z), a.y.mul(a.z).mul(b.x));
    T::axiom_eqv_transitive(
        a.z.mul(b.x).mul(a.y),
        a.y.mul(a.z).mul(b.x),
        a.y.mul(b.x).mul(a.z),
    );

    // T3+ = ax*by*az, T1- = az*by*ax: both ≡ (a_*a_)*b_
    lemma_mul_right_swap::<T>(a.x, b.y, a.z);
    lemma_mul_right_swap::<T>(a.z, b.y, a.x);
    T::axiom_mul_commutative(a.x, a.z);
    T::axiom_mul_congruence_left(a.x.mul(a.z), a.z.mul(a.x), b.y);
    T::axiom_eqv_transitive(
        a.x.mul(b.y).mul(a.z),
        a.x.mul(a.z).mul(b.y),
        a.z.mul(a.x).mul(b.y),
    );
    T::axiom_eqv_symmetric(a.z.mul(b.y).mul(a.x), a.z.mul(a.x).mul(b.y));
    T::axiom_eqv_transitive(
        a.x.mul(b.y).mul(a.z),
        a.z.mul(a.x).mul(b.y),
        a.z.mul(b.y).mul(a.x),
    );

    // Step 4: Replace positive terms with their negative-term equivalents
    // T1+ ≡ T2-, so (T1+ - T1-) ≡ (T2- - T1-)
    T::axiom_eqv_reflexive(a.z.mul(b.y).mul(a.x));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.y.mul(b.z).mul(a.x), a.x.mul(b.z).mul(a.y),
        a.z.mul(b.y).mul(a.x), a.z.mul(b.y).mul(a.x),
    );
    // T2+ ≡ T3-, so (T2+ - T2-) ≡ (T3- - T2-)
    T::axiom_eqv_reflexive(a.x.mul(b.z).mul(a.y));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.z.mul(b.x).mul(a.y), a.y.mul(b.x).mul(a.z),
        a.x.mul(b.z).mul(a.y), a.x.mul(b.z).mul(a.y),
    );
    // T3+ ≡ T1-, so (T3+ - T3-) ≡ (T1- - T3-)
    T::axiom_eqv_reflexive(a.y.mul(b.x).mul(a.z));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.x.mul(b.y).mul(a.z), a.z.mul(b.y).mul(a.x),
        a.y.mul(b.x).mul(a.z), a.y.mul(b.x).mul(a.z),
    );

    // Propagate through additions
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.y.mul(b.z).mul(a.x).sub(a.z.mul(b.y).mul(a.x)),
        a.x.mul(b.z).mul(a.y).sub(a.z.mul(b.y).mul(a.x)),
        a.z.mul(b.x).mul(a.y).sub(a.x.mul(b.z).mul(a.y)),
        a.y.mul(b.x).mul(a.z).sub(a.x.mul(b.z).mul(a.y)),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.y.mul(b.z).mul(a.x).sub(a.z.mul(b.y).mul(a.x)).add(a.z.mul(b.x).mul(a.y).sub(a.x.mul(b.z).mul(a.y))),
        a.x.mul(b.z).mul(a.y).sub(a.z.mul(b.y).mul(a.x)).add(a.y.mul(b.x).mul(a.z).sub(a.x.mul(b.z).mul(a.y))),
        a.x.mul(b.y).mul(a.z).sub(a.y.mul(b.x).mul(a.z)),
        a.z.mul(b.y).mul(a.x).sub(a.y.mul(b.x).mul(a.z)),
    );
    // Now: ≡ (T2- - T1-) + (T3- - T2-) + (T1- - T3-)
    // Let q1 = T1- = az*by*ax, q2 = T2- = ax*bz*ay, q3 = T3- = ay*bx*az

    // Step 5: Telescope (q2-q1) + (q3-q2) ≡ q3-q1
    // First commute: (q2-q1) + (q3-q2) ≡ (q3-q2) + (q2-q1)
    T::axiom_add_commutative(
        a.x.mul(b.z).mul(a.y).sub(a.z.mul(b.y).mul(a.x)),
        a.y.mul(b.x).mul(a.z).sub(a.x.mul(b.z).mul(a.y)),
    );
    // (q3-q2) + (q2-q1) ≡ q3-q1
    additive_group_lemmas::lemma_sub_add_sub::<T>(
        a.y.mul(b.x).mul(a.z),
        a.x.mul(b.z).mul(a.y),
        a.z.mul(b.y).mul(a.x),
    );
    T::axiom_eqv_transitive(
        a.x.mul(b.z).mul(a.y).sub(a.z.mul(b.y).mul(a.x)).add(a.y.mul(b.x).mul(a.z).sub(a.x.mul(b.z).mul(a.y))),
        a.y.mul(b.x).mul(a.z).sub(a.x.mul(b.z).mul(a.y)).add(a.x.mul(b.z).mul(a.y).sub(a.z.mul(b.y).mul(a.x))),
        a.y.mul(b.x).mul(a.z).sub(a.z.mul(b.y).mul(a.x)),
    );
    // (q3-q1) + (q1-q3) ≡ 0
    // Propagate: (q3-q1) + (q1-q3) into the outer add
    T::axiom_add_congruence_left(
        a.x.mul(b.z).mul(a.y).sub(a.z.mul(b.y).mul(a.x)).add(a.y.mul(b.x).mul(a.z).sub(a.x.mul(b.z).mul(a.y))),
        a.y.mul(b.x).mul(a.z).sub(a.z.mul(b.y).mul(a.x)),
        a.z.mul(b.y).mul(a.x).sub(a.y.mul(b.x).mul(a.z)),
    );
    // (q3-q1) + (q1-q3): commute then telescope
    T::axiom_add_commutative(
        a.y.mul(b.x).mul(a.z).sub(a.z.mul(b.y).mul(a.x)),
        a.z.mul(b.y).mul(a.x).sub(a.y.mul(b.x).mul(a.z)),
    );
    // (q1-q3) + (q3-q1) ≡ q1-q1 ≡ 0
    additive_group_lemmas::lemma_sub_add_sub::<T>(
        a.z.mul(b.y).mul(a.x),
        a.y.mul(b.x).mul(a.z),
        a.z.mul(b.y).mul(a.x),
    );
    additive_group_lemmas::lemma_sub_self::<T>(a.z.mul(b.y).mul(a.x));
    T::axiom_eqv_transitive(
        a.y.mul(b.x).mul(a.z).sub(a.z.mul(b.y).mul(a.x)).add(a.z.mul(b.y).mul(a.x).sub(a.y.mul(b.x).mul(a.z))),
        a.z.mul(b.y).mul(a.x).sub(a.y.mul(b.x).mul(a.z)).add(a.y.mul(b.x).mul(a.z).sub(a.z.mul(b.y).mul(a.x))),
        a.z.mul(b.y).mul(a.x).sub(a.z.mul(b.y).mul(a.x)),
    );
    T::axiom_eqv_transitive(
        a.y.mul(b.x).mul(a.z).sub(a.z.mul(b.y).mul(a.x)).add(a.z.mul(b.y).mul(a.x).sub(a.y.mul(b.x).mul(a.z))),
        a.z.mul(b.y).mul(a.x).sub(a.z.mul(b.y).mul(a.x)),
        T::zero(),
    );

    // Step 6: Chain everything together
    // dot(cross(a,b), a)
    //   ≡ (T1+-T1-) + (T2+-T2-) + (T3+-T3-)     [step 2]
    //   ≡ (q2-q1) + (q3-q2) + (q1-q3)            [step 4]
    //   ≡ (q3-q1) + (q1-q3)                        [step 5, with congruence]
    //   ≡ 0                                         [step 5 final]
    T::axiom_eqv_transitive(
        dot(cross(a, b), a),
        a.y.mul(b.z).mul(a.x).sub(a.z.mul(b.y).mul(a.x)).add(a.z.mul(b.x).mul(a.y).sub(a.x.mul(b.z).mul(a.y))).add(a.x.mul(b.y).mul(a.z).sub(a.y.mul(b.x).mul(a.z))),
        a.x.mul(b.z).mul(a.y).sub(a.z.mul(b.y).mul(a.x)).add(a.y.mul(b.x).mul(a.z).sub(a.x.mul(b.z).mul(a.y))).add(a.z.mul(b.y).mul(a.x).sub(a.y.mul(b.x).mul(a.z))),
    );
    T::axiom_eqv_transitive(
        dot(cross(a, b), a),
        a.x.mul(b.z).mul(a.y).sub(a.z.mul(b.y).mul(a.x)).add(a.y.mul(b.x).mul(a.z).sub(a.x.mul(b.z).mul(a.y))).add(a.z.mul(b.y).mul(a.x).sub(a.y.mul(b.x).mul(a.z))),
        a.y.mul(b.x).mul(a.z).sub(a.z.mul(b.y).mul(a.x)).add(a.z.mul(b.y).mul(a.x).sub(a.y.mul(b.x).mul(a.z))),
    );
    T::axiom_eqv_transitive(
        dot(cross(a, b), a),
        a.y.mul(b.x).mul(a.z).sub(a.z.mul(b.y).mul(a.x)).add(a.z.mul(b.y).mul(a.x).sub(a.y.mul(b.x).mul(a.z))),
        T::zero(),
    );
}

/// dot(cross(a, b), b) ≡ 0
pub proof fn lemma_cross_orthogonal_right<T: Ring>(a: Vec3<T>, b: Vec3<T>)
    ensures
        dot(cross(a, b), b).eqv(T::zero()),
{
    // dot(cross(a,b), b) = (ay*bz - az*by)*bx + (az*bx - ax*bz)*by + (ax*by - ay*bx)*bz
    //
    // The 6 terms after expanding:
    //   T1+ = ay*bz*bx, T1- = az*by*bx
    //   T2+ = az*bx*by, T2- = ax*bz*by
    //   T3+ = ax*by*bz, T3- = ay*bx*bz
    //
    // T1+ ≡ T3- (both ≡ ay*(bx*bz)), T2+ ≡ T1- (both ≡ az*(bx*by)), T3+ ≡ T2- (both ≡ ax*(by*bz))

    // Step 1: Expand
    ring_lemmas::lemma_sub_mul_right::<T>(a.y.mul(b.z), a.z.mul(b.y), b.x);
    ring_lemmas::lemma_sub_mul_right::<T>(a.z.mul(b.x), a.x.mul(b.z), b.y);
    ring_lemmas::lemma_sub_mul_right::<T>(a.x.mul(b.y), a.y.mul(b.x), b.z);

    // Step 2: Propagate
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.y.mul(b.z).sub(a.z.mul(b.y)).mul(b.x),
        a.y.mul(b.z).mul(b.x).sub(a.z.mul(b.y).mul(b.x)),
        a.z.mul(b.x).sub(a.x.mul(b.z)).mul(b.y),
        a.z.mul(b.x).mul(b.y).sub(a.x.mul(b.z).mul(b.y)),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.y.mul(b.z).sub(a.z.mul(b.y)).mul(b.x).add(a.z.mul(b.x).sub(a.x.mul(b.z)).mul(b.y)),
        a.y.mul(b.z).mul(b.x).sub(a.z.mul(b.y).mul(b.x)).add(a.z.mul(b.x).mul(b.y).sub(a.x.mul(b.z).mul(b.y))),
        a.x.mul(b.y).sub(a.y.mul(b.x)).mul(b.z),
        a.x.mul(b.y).mul(b.z).sub(a.y.mul(b.x).mul(b.z)),
    );

    // Step 3: Show pairwise equivalences
    // T1+ = (ay*bz)*bx ≡ ay*(bx*bz) and T3- = (ay*bx)*bz ≡ ay*(bx*bz)
    lemma_mul_right_swap::<T>(a.y, b.z, b.x);
    lemma_mul_right_swap::<T>(a.y, b.x, b.z);
    T::axiom_mul_commutative(b.z, b.x);
    ring_lemmas::lemma_mul_congruence_right::<T>(a.y, b.z.mul(b.x), b.x.mul(b.z));
    // (ay*bz)*bx ≡ ay*(bz*bx) (from right_swap, but we got ay*bx*bz)
    // Actually lemma_mul_right_swap(ay, bz, bx) gives: (ay*bz)*bx ≡ (ay*bx)*bz = T3-
    // So T1+ ≡ T3- directly!
    // Wait, lemma_mul_right_swap(a, b, c) gives a.mul(b).mul(c) ≡ a.mul(c).mul(b)
    // So lemma_mul_right_swap(ay, bz, bx) gives (ay*bz)*bx ≡ (ay*bx)*bz ✓

    // T2+ = (az*bx)*by ≡ (az*by)*bx = T1-
    lemma_mul_right_swap::<T>(a.z, b.x, b.y);

    // T3+ = (ax*by)*bz ≡ (ax*bz)*by = T2-
    lemma_mul_right_swap::<T>(a.x, b.y, b.z);

    // Step 4: Replace using sub_congruence
    // Need reflexive for the unchanged side
    T::axiom_eqv_reflexive(a.z.mul(b.y).mul(b.x));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.y.mul(b.z).mul(b.x), a.y.mul(b.x).mul(b.z),
        a.z.mul(b.y).mul(b.x), a.z.mul(b.y).mul(b.x),
    );
    T::axiom_eqv_reflexive(a.x.mul(b.z).mul(b.y));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.z.mul(b.x).mul(b.y), a.z.mul(b.y).mul(b.x),
        a.x.mul(b.z).mul(b.y), a.x.mul(b.z).mul(b.y),
    );
    T::axiom_eqv_reflexive(a.y.mul(b.x).mul(b.z));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.x.mul(b.y).mul(b.z), a.x.mul(b.z).mul(b.y),
        a.y.mul(b.x).mul(b.z), a.y.mul(b.x).mul(b.z),
    );

    // Propagate
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.y.mul(b.z).mul(b.x).sub(a.z.mul(b.y).mul(b.x)),
        a.y.mul(b.x).mul(b.z).sub(a.z.mul(b.y).mul(b.x)),
        a.z.mul(b.x).mul(b.y).sub(a.x.mul(b.z).mul(b.y)),
        a.z.mul(b.y).mul(b.x).sub(a.x.mul(b.z).mul(b.y)),
    );
    additive_commutative_monoid_lemmas::lemma_add_congruence::<T>(
        a.y.mul(b.z).mul(b.x).sub(a.z.mul(b.y).mul(b.x)).add(a.z.mul(b.x).mul(b.y).sub(a.x.mul(b.z).mul(b.y))),
        a.y.mul(b.x).mul(b.z).sub(a.z.mul(b.y).mul(b.x)).add(a.z.mul(b.y).mul(b.x).sub(a.x.mul(b.z).mul(b.y))),
        a.x.mul(b.y).mul(b.z).sub(a.y.mul(b.x).mul(b.z)),
        a.x.mul(b.z).mul(b.y).sub(a.y.mul(b.x).mul(b.z)),
    );
    // Now: ≡ (q3-q1) + (q1-q2) + (q2-q3)
    // where q1 = az*by*bx, q2 = ax*bz*by, q3 = ay*bx*bz

    // Step 5: Telescope
    // (q3-q1) + (q1-q2) ≡ q3-q2 via sub_add_sub(q3, q1, q2)
    additive_group_lemmas::lemma_sub_add_sub::<T>(
        a.y.mul(b.x).mul(b.z),
        a.z.mul(b.y).mul(b.x),
        a.x.mul(b.z).mul(b.y),
    );
    // (q3-q2) + (q2-q3): telescope
    T::axiom_add_congruence_left(
        a.y.mul(b.x).mul(b.z).sub(a.z.mul(b.y).mul(b.x)).add(a.z.mul(b.y).mul(b.x).sub(a.x.mul(b.z).mul(b.y))),
        a.y.mul(b.x).mul(b.z).sub(a.x.mul(b.z).mul(b.y)),
        a.x.mul(b.z).mul(b.y).sub(a.y.mul(b.x).mul(b.z)),
    );
    // (q3-q2) + (q2-q3): commute then telescope
    T::axiom_add_commutative(
        a.y.mul(b.x).mul(b.z).sub(a.x.mul(b.z).mul(b.y)),
        a.x.mul(b.z).mul(b.y).sub(a.y.mul(b.x).mul(b.z)),
    );
    additive_group_lemmas::lemma_sub_add_sub::<T>(
        a.x.mul(b.z).mul(b.y),
        a.y.mul(b.x).mul(b.z),
        a.x.mul(b.z).mul(b.y),
    );
    additive_group_lemmas::lemma_sub_self::<T>(a.x.mul(b.z).mul(b.y));
    T::axiom_eqv_transitive(
        a.y.mul(b.x).mul(b.z).sub(a.x.mul(b.z).mul(b.y)).add(a.x.mul(b.z).mul(b.y).sub(a.y.mul(b.x).mul(b.z))),
        a.x.mul(b.z).mul(b.y).sub(a.y.mul(b.x).mul(b.z)).add(a.y.mul(b.x).mul(b.z).sub(a.x.mul(b.z).mul(b.y))),
        a.x.mul(b.z).mul(b.y).sub(a.x.mul(b.z).mul(b.y)),
    );
    T::axiom_eqv_transitive(
        a.y.mul(b.x).mul(b.z).sub(a.x.mul(b.z).mul(b.y)).add(a.x.mul(b.z).mul(b.y).sub(a.y.mul(b.x).mul(b.z))),
        a.x.mul(b.z).mul(b.y).sub(a.x.mul(b.z).mul(b.y)),
        T::zero(),
    );

    // Step 6: Chain everything
    T::axiom_eqv_transitive(
        dot(cross(a, b), b),
        a.y.mul(b.z).mul(b.x).sub(a.z.mul(b.y).mul(b.x)).add(a.z.mul(b.x).mul(b.y).sub(a.x.mul(b.z).mul(b.y))).add(a.x.mul(b.y).mul(b.z).sub(a.y.mul(b.x).mul(b.z))),
        a.y.mul(b.x).mul(b.z).sub(a.z.mul(b.y).mul(b.x)).add(a.z.mul(b.y).mul(b.x).sub(a.x.mul(b.z).mul(b.y))).add(a.x.mul(b.z).mul(b.y).sub(a.y.mul(b.x).mul(b.z))),
    );
    T::axiom_eqv_transitive(
        dot(cross(a, b), b),
        a.y.mul(b.x).mul(b.z).sub(a.z.mul(b.y).mul(b.x)).add(a.z.mul(b.y).mul(b.x).sub(a.x.mul(b.z).mul(b.y))).add(a.x.mul(b.z).mul(b.y).sub(a.y.mul(b.x).mul(b.z))),
        a.y.mul(b.x).mul(b.z).sub(a.x.mul(b.z).mul(b.y)).add(a.x.mul(b.z).mul(b.y).sub(a.y.mul(b.x).mul(b.z))),
    );
    T::axiom_eqv_transitive(
        dot(cross(a, b), b),
        a.y.mul(b.x).mul(b.z).sub(a.x.mul(b.z).mul(b.y)).add(a.x.mul(b.z).mul(b.y).sub(a.y.mul(b.x).mul(b.z))),
        T::zero(),
    );
}

} // verus!
