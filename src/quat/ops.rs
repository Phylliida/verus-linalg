use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use super::Quat;

verus! {

// ===========================================================================
// Spec functions
// ===========================================================================

/// Scalar multiplication: scale(s, q) = (s*w, s*x, s*y, s*z)
pub open spec fn scale<T: Ring>(s: T, q: Quat<T>) -> Quat<T> {
    Quat { w: s.mul(q.w), x: s.mul(q.x), y: s.mul(q.y), z: s.mul(q.z) }
}

/// Hamilton product
pub open spec fn mul<T: Ring>(a: Quat<T>, b: Quat<T>) -> Quat<T> {
    Quat {
        w: a.w.mul(b.w).sub(a.x.mul(b.x)).sub(a.y.mul(b.y)).sub(a.z.mul(b.z)),
        x: a.w.mul(b.x).add(a.x.mul(b.w)).add(a.y.mul(b.z)).sub(a.z.mul(b.y)),
        y: a.w.mul(b.y).sub(a.x.mul(b.z)).add(a.y.mul(b.w)).add(a.z.mul(b.x)),
        z: a.w.mul(b.z).add(a.x.mul(b.y)).sub(a.y.mul(b.x)).add(a.z.mul(b.w)),
    }
}

/// Conjugate: (w, -x, -y, -z)
pub open spec fn conjugate<T: Ring>(q: Quat<T>) -> Quat<T> {
    Quat { w: q.w, x: q.x.neg(), y: q.y.neg(), z: q.z.neg() }
}

/// Squared norm: w² + x² + y² + z²
pub open spec fn norm_sq<T: Ring>(q: Quat<T>) -> T {
    q.w.mul(q.w).add(q.x.mul(q.x)).add(q.y.mul(q.y)).add(q.z.mul(q.z))
}

/// Multiplicative identity (1, 0, 0, 0)
pub open spec fn one<T: Ring>() -> Quat<T> {
    Quat { w: T::one(), x: T::zero(), y: T::zero(), z: T::zero() }
}

/// Basis element i: (0, 1, 0, 0)
pub open spec fn qi<T: Ring>() -> Quat<T> {
    Quat { w: T::zero(), x: T::one(), y: T::zero(), z: T::zero() }
}

/// Basis element j: (0, 0, 1, 0)
pub open spec fn qj<T: Ring>() -> Quat<T> {
    Quat { w: T::zero(), x: T::zero(), y: T::one(), z: T::zero() }
}

/// Basis element k: (0, 0, 0, 1)
pub open spec fn qk<T: Ring>() -> Quat<T> {
    Quat { w: T::zero(), x: T::zero(), y: T::zero(), z: T::one() }
}

/// Basis by index: 0→1, 1→i, 2→j, 3→k
pub open spec fn basis<T: Ring>(i: int) -> Quat<T>
    recommends 0 <= i < 4,
{
    if i == 0 { one() }
    else if i == 1 { qi() }
    else if i == 2 { qj() }
    else { qk() }
}

/// Signed basis: basis(i) scaled by sign
pub open spec fn signed_basis<T: Ring>(sign: T, i: int) -> Quat<T>
    recommends 0 <= i < 4,
{
    scale(sign, basis(i))
}

/// Bridge to Vec4 for reusing dot/norm lemmas
pub open spec fn as_vec4<T: Ring>(q: Quat<T>) -> crate::vec4::Vec4<T> {
    crate::vec4::Vec4 { x: q.w, y: q.x, z: q.y, w: q.z }
}

// ===========================================================================
// Scalar helpers
// ===========================================================================

/// a - 0 ≡ a
pub proof fn lemma_sub_zero<T: Ring>(a: T)
    ensures a.sub(T::zero()).eqv(a),
{
    T::axiom_sub_is_add_neg(a, T::zero());
    additive_group_lemmas::lemma_neg_zero::<T>();
    additive_group_lemmas::lemma_add_congruence_right::<T>(a, T::zero().neg(), T::zero());
    T::axiom_add_zero_right(a);
    T::axiom_eqv_transitive(a.sub(T::zero()), a.add(T::zero().neg()), a.add(T::zero()));
    T::axiom_eqv_transitive(a.sub(T::zero()), a.add(T::zero()), a);
}

/// (a+b) - (c+d) ≡ (a-c) + (b-d)
pub proof fn lemma_sub_add_rearrange<T: Ring>(a: T, b: T, c: T, d: T)
    ensures a.add(b).sub(c.add(d)).eqv(a.sub(c).add(b.sub(d))),
{
    // (a+b) - (c+d) = (a+b) + (-(c+d)) = (a+b) + (-c + -d)
    T::axiom_sub_is_add_neg(a.add(b), c.add(d));
    additive_group_lemmas::lemma_neg_add::<T>(c, d);
    additive_group_lemmas::lemma_add_congruence_right::<T>(a.add(b), c.add(d).neg(), c.neg().add(d.neg()));
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(b).add(c.add(d).neg()),
        a.add(b).add(c.neg().add(d.neg())),
    );
    // Rearrange: (a+b) + (-c+-d) ≡ (a+-c) + (b+-d)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a, b, c.neg(), d.neg());
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(b).add(c.neg().add(d.neg())),
        a.add(c.neg()).add(b.add(d.neg())),
    );
    // Convert add_neg back to sub
    T::axiom_sub_is_add_neg(a, c);
    T::axiom_eqv_symmetric(a.sub(c), a.add(c.neg()));
    T::axiom_sub_is_add_neg(b, d);
    T::axiom_eqv_symmetric(b.sub(d), b.add(d.neg()));
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(c.neg()), a.sub(c), b.add(d.neg()), b.sub(d),
    );
    T::axiom_eqv_transitive(
        a.add(b).sub(c.add(d)),
        a.add(c.neg()).add(b.add(d.neg())),
        a.sub(c).add(b.sub(d)),
    );
}

/// (a+b) + (c+d) ≡ (a+c) + (b+d)
pub proof fn lemma_add_add_rearrange<T: Ring>(a: T, b: T, c: T, d: T)
    ensures a.add(b).add(c.add(d)).eqv(a.add(c).add(b.add(d))),
{
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(a, b, c, d);
}

// ===========================================================================
// Scale lemmas
// ===========================================================================

/// scale(s, a + b) ≡ scale(s, a) + scale(s, b)
pub proof fn lemma_scale_distributes_over_add<T: Ring>(s: T, a: Quat<T>, b: Quat<T>)
    ensures scale(s, a.add(b)).eqv(scale(s, a).add(scale(s, b))),
{
    T::axiom_mul_distributes_left(s, a.w, b.w);
    T::axiom_mul_distributes_left(s, a.x, b.x);
    T::axiom_mul_distributes_left(s, a.y, b.y);
    T::axiom_mul_distributes_left(s, a.z, b.z);
}

/// scale(s + t, a) ≡ scale(s, a) + scale(t, a)
pub proof fn lemma_scale_add_distributes<T: Ring>(s: T, t: T, a: Quat<T>)
    ensures scale(s.add(t), a).eqv(scale(s, a).add(scale(t, a))),
{
    ring_lemmas::lemma_mul_distributes_right::<T>(s, t, a.w);
    ring_lemmas::lemma_mul_distributes_right::<T>(s, t, a.x);
    ring_lemmas::lemma_mul_distributes_right::<T>(s, t, a.y);
    ring_lemmas::lemma_mul_distributes_right::<T>(s, t, a.z);
}

/// scale(1, a) ≡ a
pub proof fn lemma_scale_identity<T: Ring>(a: Quat<T>)
    ensures scale(T::one(), a).eqv(a),
{
    ring_lemmas::lemma_mul_one_left::<T>(a.w);
    ring_lemmas::lemma_mul_one_left::<T>(a.x);
    ring_lemmas::lemma_mul_one_left::<T>(a.y);
    ring_lemmas::lemma_mul_one_left::<T>(a.z);
}

/// scale(0, a) ≡ zero
pub proof fn lemma_scale_zero_scalar<T: Ring>(a: Quat<T>)
    ensures scale(T::zero(), a).eqv(Quat::<T>::zero()),
{
    ring_lemmas::lemma_mul_zero_left::<T>(a.w);
    ring_lemmas::lemma_mul_zero_left::<T>(a.x);
    ring_lemmas::lemma_mul_zero_left::<T>(a.y);
    ring_lemmas::lemma_mul_zero_left::<T>(a.z);
}

/// scale(s, zero) ≡ zero
pub proof fn lemma_scale_zero_vec<T: Ring>(s: T)
    ensures scale(s, Quat::<T>::zero()).eqv(Quat::<T>::zero()),
{
    T::axiom_mul_zero_right(s);
}

/// a ≡ b implies scale(s, a) ≡ scale(s, b)
pub proof fn lemma_scale_congruence<T: Ring>(s: T, a: Quat<T>, b: Quat<T>)
    requires a.eqv(b),
    ensures scale(s, a).eqv(scale(s, b)),
{
    ring_lemmas::lemma_mul_congruence_right::<T>(s, a.w, b.w);
    ring_lemmas::lemma_mul_congruence_right::<T>(s, a.x, b.x);
    ring_lemmas::lemma_mul_congruence_right::<T>(s, a.y, b.y);
    ring_lemmas::lemma_mul_congruence_right::<T>(s, a.z, b.z);
}

/// s ≡ t implies scale(s, a) ≡ scale(t, a)
pub proof fn lemma_scale_congruence_scalar<T: Ring>(s: T, t: T, a: Quat<T>)
    requires s.eqv(t),
    ensures scale(s, a).eqv(scale(t, a)),
{
    T::axiom_mul_congruence_left(s, t, a.w);
    T::axiom_mul_congruence_left(s, t, a.x);
    T::axiom_mul_congruence_left(s, t, a.y);
    T::axiom_mul_congruence_left(s, t, a.z);
}

/// scale(s, scale(t, a)) ≡ scale(s * t, a)
pub proof fn lemma_scale_associative<T: Ring>(s: T, t: T, a: Quat<T>)
    ensures scale(s, scale(t, a)).eqv(scale(s.mul(t), a)),
{
    T::axiom_mul_associative(s, t, a.w);
    T::axiom_eqv_symmetric(s.mul(t).mul(a.w), s.mul(t.mul(a.w)));
    T::axiom_mul_associative(s, t, a.x);
    T::axiom_eqv_symmetric(s.mul(t).mul(a.x), s.mul(t.mul(a.x)));
    T::axiom_mul_associative(s, t, a.y);
    T::axiom_eqv_symmetric(s.mul(t).mul(a.y), s.mul(t.mul(a.y)));
    T::axiom_mul_associative(s, t, a.z);
    T::axiom_eqv_symmetric(s.mul(t).mul(a.z), s.mul(t.mul(a.z)));
}

/// scale(-s, a) ≡ -scale(s, a)
pub proof fn lemma_scale_neg_scalar<T: Ring>(s: T, a: Quat<T>)
    ensures scale(s.neg(), a).eqv(scale(s, a).neg()),
{
    ring_lemmas::lemma_mul_neg_left::<T>(s, a.w);
    ring_lemmas::lemma_mul_neg_left::<T>(s, a.x);
    ring_lemmas::lemma_mul_neg_left::<T>(s, a.y);
    ring_lemmas::lemma_mul_neg_left::<T>(s, a.z);
}

/// scale(s, -a) ≡ -scale(s, a)
pub proof fn lemma_scale_neg_vec<T: Ring>(s: T, a: Quat<T>)
    ensures scale(s, a.neg()).eqv(scale(s, a).neg()),
{
    ring_lemmas::lemma_mul_neg_right::<T>(s, a.w);
    ring_lemmas::lemma_mul_neg_right::<T>(s, a.x);
    ring_lemmas::lemma_mul_neg_right::<T>(s, a.y);
    ring_lemmas::lemma_mul_neg_right::<T>(s, a.z);
}

/// scale(s, a - b) ≡ scale(s, a) - scale(s, b)
pub proof fn lemma_scale_sub_distributes<T: Ring>(s: T, a: Quat<T>, b: Quat<T>)
    ensures scale(s, a.sub(b)).eqv(scale(s, a).sub(scale(s, b))),
{
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.w, b.w);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.x, b.x);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.y, b.y);
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.z, b.z);
}

// ===========================================================================
// Mul identity lemmas
// ===========================================================================

/// mul(one(), q) ≡ q
pub proof fn lemma_mul_one_left<T: Ring>(q: Quat<T>)
    ensures mul(one(), q).eqv(q),
{
    let o = T::one();
    let z = T::zero();
    // Establish all product simplifications
    ring_lemmas::lemma_mul_one_left::<T>(q.w);
    ring_lemmas::lemma_mul_one_left::<T>(q.x);
    ring_lemmas::lemma_mul_one_left::<T>(q.y);
    ring_lemmas::lemma_mul_one_left::<T>(q.z);
    ring_lemmas::lemma_mul_zero_left::<T>(q.w);
    ring_lemmas::lemma_mul_zero_left::<T>(q.x);
    ring_lemmas::lemma_mul_zero_left::<T>(q.y);
    ring_lemmas::lemma_mul_zero_left::<T>(q.z);
    T::axiom_eqv_reflexive(z);
    T::axiom_eqv_reflexive(q.w);
    T::axiom_eqv_reflexive(q.x);
    T::axiom_eqv_reflexive(q.y);
    T::axiom_eqv_reflexive(q.z);
    lemma_sub_zero::<T>(q.w);
    lemma_sub_zero::<T>(q.x);
    lemma_sub_zero::<T>(q.y);
    lemma_sub_zero::<T>(q.z);

    // w: 1*qw - 0*qx - 0*qy - 0*qz ≡ qw - 0 - 0 - 0 ≡ qw
    additive_group_lemmas::lemma_sub_congruence::<T>(o.mul(q.w), q.w, z.mul(q.x), z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        o.mul(q.w).sub(z.mul(q.x)), q.w.sub(z), z.mul(q.y), z,
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        o.mul(q.w).sub(z.mul(q.x)).sub(z.mul(q.y)), q.w.sub(z).sub(z), z.mul(q.z), z,
    );
    // qw.sub(z).sub(z).sub(z) ≡ qw
    additive_group_lemmas::lemma_sub_congruence::<T>(q.w.sub(z), q.w, z, z);
    T::axiom_eqv_transitive(q.w.sub(z).sub(z), q.w.sub(z), q.w);
    additive_group_lemmas::lemma_sub_congruence::<T>(q.w.sub(z).sub(z), q.w, z, z);
    T::axiom_eqv_transitive(q.w.sub(z).sub(z).sub(z), q.w.sub(z), q.w);
    T::axiom_eqv_transitive(mul(one::<T>(), q).w, q.w.sub(z).sub(z).sub(z), q.w);

    // x: 1*qx + 0*qw + 0*qz - 0*qy ≡ qx + 0 + 0 - 0 ≡ qx
    additive_group_lemmas::lemma_add_congruence::<T>(o.mul(q.x), q.x, z.mul(q.w), z);
    T::axiom_add_zero_right(q.x);
    T::axiom_eqv_transitive(o.mul(q.x).add(z.mul(q.w)), q.x.add(z), q.x);
    additive_group_lemmas::lemma_add_congruence::<T>(
        o.mul(q.x).add(z.mul(q.w)), q.x, z.mul(q.z), z,
    );
    T::axiom_add_zero_right(q.x);
    T::axiom_eqv_transitive(o.mul(q.x).add(z.mul(q.w)).add(z.mul(q.z)), q.x.add(z), q.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        o.mul(q.x).add(z.mul(q.w)).add(z.mul(q.z)), q.x, z.mul(q.y), z,
    );
    T::axiom_eqv_transitive(
        mul(one::<T>(), q).x, q.x.sub(z), q.x,
    );

    // y: 1*qy - 0*qz + 0*qw + 0*qx ≡ qy - 0 + 0 + 0 ≡ qy
    additive_group_lemmas::lemma_sub_congruence::<T>(o.mul(q.y), q.y, z.mul(q.z), z);
    T::axiom_eqv_transitive(o.mul(q.y).sub(z.mul(q.z)), q.y.sub(z), q.y);
    additive_group_lemmas::lemma_add_congruence::<T>(
        o.mul(q.y).sub(z.mul(q.z)), q.y, z.mul(q.w), z,
    );
    T::axiom_add_zero_right(q.y);
    T::axiom_eqv_transitive(o.mul(q.y).sub(z.mul(q.z)).add(z.mul(q.w)), q.y.add(z), q.y);
    additive_group_lemmas::lemma_add_congruence::<T>(
        o.mul(q.y).sub(z.mul(q.z)).add(z.mul(q.w)), q.y, z.mul(q.x), z,
    );
    T::axiom_add_zero_right(q.y);
    T::axiom_eqv_transitive(
        mul(one::<T>(), q).y, q.y.add(z), q.y,
    );

    // z: 1*qz + 0*qy - 0*qx + 0*qw ≡ qz + 0 - 0 + 0 ≡ qz
    additive_group_lemmas::lemma_add_congruence::<T>(o.mul(q.z), q.z, z.mul(q.y), z);
    T::axiom_add_zero_right(q.z);
    T::axiom_eqv_transitive(o.mul(q.z).add(z.mul(q.y)), q.z.add(z), q.z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        o.mul(q.z).add(z.mul(q.y)), q.z, z.mul(q.x), z,
    );
    T::axiom_eqv_transitive(o.mul(q.z).add(z.mul(q.y)).sub(z.mul(q.x)), q.z.sub(z), q.z);
    additive_group_lemmas::lemma_add_congruence::<T>(
        o.mul(q.z).add(z.mul(q.y)).sub(z.mul(q.x)), q.z, z.mul(q.w), z,
    );
    T::axiom_add_zero_right(q.z);
    T::axiom_eqv_transitive(
        mul(one::<T>(), q).z, q.z.add(z), q.z,
    );
}

/// mul(q, one()) ≡ q
pub proof fn lemma_mul_one_right<T: Ring>(q: Quat<T>)
    ensures mul(q, one()).eqv(q),
{
    let o = T::one();
    let z = T::zero();
    T::axiom_mul_one_right(q.w);
    T::axiom_mul_one_right(q.x);
    T::axiom_mul_one_right(q.y);
    T::axiom_mul_one_right(q.z);
    T::axiom_mul_zero_right(q.w);
    T::axiom_mul_zero_right(q.x);
    T::axiom_mul_zero_right(q.y);
    T::axiom_mul_zero_right(q.z);
    T::axiom_eqv_reflexive(z);
    T::axiom_eqv_reflexive(q.w);
    T::axiom_eqv_reflexive(q.x);
    T::axiom_eqv_reflexive(q.y);
    T::axiom_eqv_reflexive(q.z);
    lemma_sub_zero::<T>(q.w);
    lemma_sub_zero::<T>(q.x);
    lemma_sub_zero::<T>(q.y);
    lemma_sub_zero::<T>(q.z);
    additive_group_lemmas::lemma_add_zero_left::<T>(q.x);
    additive_group_lemmas::lemma_add_zero_left::<T>(q.y);
    additive_group_lemmas::lemma_add_zero_left::<T>(q.z);

    // w: qw*1 - qx*0 - qy*0 - qz*0 ≡ qw - 0 - 0 - 0 ≡ qw
    additive_group_lemmas::lemma_sub_congruence::<T>(q.w.mul(o), q.w, q.x.mul(z), z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        q.w.mul(o).sub(q.x.mul(z)), q.w.sub(z), q.y.mul(z), z,
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        q.w.mul(o).sub(q.x.mul(z)).sub(q.y.mul(z)), q.w.sub(z).sub(z), q.z.mul(z), z,
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(q.w.sub(z), q.w, z, z);
    T::axiom_eqv_transitive(q.w.sub(z).sub(z), q.w.sub(z), q.w);
    additive_group_lemmas::lemma_sub_congruence::<T>(q.w.sub(z).sub(z), q.w, z, z);
    T::axiom_eqv_transitive(q.w.sub(z).sub(z).sub(z), q.w.sub(z), q.w);
    T::axiom_eqv_transitive(mul(q, one::<T>()).w, q.w.sub(z).sub(z).sub(z), q.w);

    // x: qw*0 + qx*1 + qy*0 - qz*0 ≡ 0 + qx + 0 - 0 ≡ qx
    additive_group_lemmas::lemma_add_congruence::<T>(q.w.mul(z), z, q.x.mul(o), q.x);
    // z+qx ≡ qx
    T::axiom_eqv_transitive(q.w.mul(z).add(q.x.mul(o)), z.add(q.x), q.x);
    additive_group_lemmas::lemma_add_congruence::<T>(
        q.w.mul(z).add(q.x.mul(o)), q.x, q.y.mul(z), z,
    );
    T::axiom_add_zero_right(q.x);
    T::axiom_eqv_transitive(
        q.w.mul(z).add(q.x.mul(o)).add(q.y.mul(z)), q.x.add(z), q.x,
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        q.w.mul(z).add(q.x.mul(o)).add(q.y.mul(z)), q.x, q.z.mul(z), z,
    );
    T::axiom_eqv_transitive(mul(q, one::<T>()).x, q.x.sub(z), q.x);

    // y: qw*0 - qx*0 + qy*1 + qz*0 ≡ 0 - 0 + qy + 0 ≡ qy
    additive_group_lemmas::lemma_sub_congruence::<T>(q.w.mul(z), z, q.x.mul(z), z);
    additive_group_lemmas::lemma_sub_self::<T>(z);
    T::axiom_eqv_transitive(q.w.mul(z).sub(q.x.mul(z)), z.sub(z), z);
    additive_group_lemmas::lemma_add_congruence::<T>(
        q.w.mul(z).sub(q.x.mul(z)), z, q.y.mul(o), q.y,
    );
    T::axiom_eqv_transitive(
        q.w.mul(z).sub(q.x.mul(z)).add(q.y.mul(o)), z.add(q.y), q.y,
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        q.w.mul(z).sub(q.x.mul(z)).add(q.y.mul(o)), q.y, q.z.mul(z), z,
    );
    T::axiom_add_zero_right(q.y);
    T::axiom_eqv_transitive(mul(q, one::<T>()).y, q.y.add(z), q.y);

    // z: qw*0 + qx*0 - qy*0 + qz*1 ≡ 0 + 0 - 0 + qz ≡ qz
    additive_group_lemmas::lemma_add_congruence::<T>(q.w.mul(z), z, q.x.mul(z), z);
    T::axiom_add_zero_right(z);
    T::axiom_eqv_transitive(q.w.mul(z).add(q.x.mul(z)), z.add(z), z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        q.w.mul(z).add(q.x.mul(z)), z, q.y.mul(z), z,
    );
    T::axiom_eqv_transitive(q.w.mul(z).add(q.x.mul(z)).sub(q.y.mul(z)), z.sub(z), z);
    additive_group_lemmas::lemma_add_congruence::<T>(
        q.w.mul(z).add(q.x.mul(z)).sub(q.y.mul(z)), z, q.z.mul(o), q.z,
    );
    T::axiom_eqv_transitive(mul(q, one::<T>()).z, z.add(q.z), q.z);
}

// ===========================================================================
// Mul congruence lemmas
// ===========================================================================

/// mul(a1, b) ≡ mul(a2, b) when a1 ≡ a2
pub proof fn lemma_mul_congruence_left<T: Ring>(a1: Quat<T>, a2: Quat<T>, b: Quat<T>)
    requires a1.eqv(a2),
    ensures mul(a1, b).eqv(mul(a2, b)),
{
    // w component
    T::axiom_mul_congruence_left(a1.w, a2.w, b.w);
    T::axiom_mul_congruence_left(a1.x, a2.x, b.x);
    T::axiom_mul_congruence_left(a1.y, a2.y, b.y);
    T::axiom_mul_congruence_left(a1.z, a2.z, b.z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a1.w.mul(b.w), a2.w.mul(b.w), a1.x.mul(b.x), a2.x.mul(b.x),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a1.w.mul(b.w).sub(a1.x.mul(b.x)), a2.w.mul(b.w).sub(a2.x.mul(b.x)),
        a1.y.mul(b.y), a2.y.mul(b.y),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a1.w.mul(b.w).sub(a1.x.mul(b.x)).sub(a1.y.mul(b.y)),
        a2.w.mul(b.w).sub(a2.x.mul(b.x)).sub(a2.y.mul(b.y)),
        a1.z.mul(b.z), a2.z.mul(b.z),
    );

    // x component
    T::axiom_mul_congruence_left(a1.w, a2.w, b.x);
    T::axiom_mul_congruence_left(a1.x, a2.x, b.w);
    T::axiom_mul_congruence_left(a1.y, a2.y, b.z);
    T::axiom_mul_congruence_left(a1.z, a2.z, b.y);
    additive_group_lemmas::lemma_add_congruence::<T>(
        a1.w.mul(b.x), a2.w.mul(b.x), a1.x.mul(b.w), a2.x.mul(b.w),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a1.w.mul(b.x).add(a1.x.mul(b.w)), a2.w.mul(b.x).add(a2.x.mul(b.w)),
        a1.y.mul(b.z), a2.y.mul(b.z),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a1.w.mul(b.x).add(a1.x.mul(b.w)).add(a1.y.mul(b.z)),
        a2.w.mul(b.x).add(a2.x.mul(b.w)).add(a2.y.mul(b.z)),
        a1.z.mul(b.y), a2.z.mul(b.y),
    );

    // y component
    T::axiom_mul_congruence_left(a1.w, a2.w, b.y);
    T::axiom_mul_congruence_left(a1.x, a2.x, b.z);
    T::axiom_mul_congruence_left(a1.y, a2.y, b.w);
    T::axiom_mul_congruence_left(a1.z, a2.z, b.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a1.w.mul(b.y), a2.w.mul(b.y), a1.x.mul(b.z), a2.x.mul(b.z),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a1.w.mul(b.y).sub(a1.x.mul(b.z)), a2.w.mul(b.y).sub(a2.x.mul(b.z)),
        a1.y.mul(b.w), a2.y.mul(b.w),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a1.w.mul(b.y).sub(a1.x.mul(b.z)).add(a1.y.mul(b.w)),
        a2.w.mul(b.y).sub(a2.x.mul(b.z)).add(a2.y.mul(b.w)),
        a1.z.mul(b.x), a2.z.mul(b.x),
    );

    // z component
    T::axiom_mul_congruence_left(a1.w, a2.w, b.z);
    T::axiom_mul_congruence_left(a1.x, a2.x, b.y);
    T::axiom_mul_congruence_left(a1.y, a2.y, b.x);
    T::axiom_mul_congruence_left(a1.z, a2.z, b.w);
    additive_group_lemmas::lemma_add_congruence::<T>(
        a1.w.mul(b.z), a2.w.mul(b.z), a1.x.mul(b.y), a2.x.mul(b.y),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a1.w.mul(b.z).add(a1.x.mul(b.y)), a2.w.mul(b.z).add(a2.x.mul(b.y)),
        a1.y.mul(b.x), a2.y.mul(b.x),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a1.w.mul(b.z).add(a1.x.mul(b.y)).sub(a1.y.mul(b.x)),
        a2.w.mul(b.z).add(a2.x.mul(b.y)).sub(a2.y.mul(b.x)),
        a1.z.mul(b.w), a2.z.mul(b.w),
    );
}

/// mul(a, b1) ≡ mul(a, b2) when b1 ≡ b2
pub proof fn lemma_mul_congruence_right<T: Ring>(a: Quat<T>, b1: Quat<T>, b2: Quat<T>)
    requires b1.eqv(b2),
    ensures mul(a, b1).eqv(mul(a, b2)),
{
    // w component
    ring_lemmas::lemma_mul_congruence_right::<T>(a.w, b1.w, b2.w);
    ring_lemmas::lemma_mul_congruence_right::<T>(a.x, b1.x, b2.x);
    ring_lemmas::lemma_mul_congruence_right::<T>(a.y, b1.y, b2.y);
    ring_lemmas::lemma_mul_congruence_right::<T>(a.z, b1.z, b2.z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(b1.w), a.w.mul(b2.w), a.x.mul(b1.x), a.x.mul(b2.x),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(b1.w).sub(a.x.mul(b1.x)), a.w.mul(b2.w).sub(a.x.mul(b2.x)),
        a.y.mul(b1.y), a.y.mul(b2.y),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(b1.w).sub(a.x.mul(b1.x)).sub(a.y.mul(b1.y)),
        a.w.mul(b2.w).sub(a.x.mul(b2.x)).sub(a.y.mul(b2.y)),
        a.z.mul(b1.z), a.z.mul(b2.z),
    );

    // x component
    ring_lemmas::lemma_mul_congruence_right::<T>(a.w, b1.x, b2.x);
    ring_lemmas::lemma_mul_congruence_right::<T>(a.x, b1.w, b2.w);
    ring_lemmas::lemma_mul_congruence_right::<T>(a.y, b1.z, b2.z);
    ring_lemmas::lemma_mul_congruence_right::<T>(a.z, b1.y, b2.y);
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(b1.x), a.w.mul(b2.x), a.x.mul(b1.w), a.x.mul(b2.w),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(b1.x).add(a.x.mul(b1.w)), a.w.mul(b2.x).add(a.x.mul(b2.w)),
        a.y.mul(b1.z), a.y.mul(b2.z),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(b1.x).add(a.x.mul(b1.w)).add(a.y.mul(b1.z)),
        a.w.mul(b2.x).add(a.x.mul(b2.w)).add(a.y.mul(b2.z)),
        a.z.mul(b1.y), a.z.mul(b2.y),
    );

    // y component
    ring_lemmas::lemma_mul_congruence_right::<T>(a.w, b1.y, b2.y);
    ring_lemmas::lemma_mul_congruence_right::<T>(a.x, b1.z, b2.z);
    ring_lemmas::lemma_mul_congruence_right::<T>(a.y, b1.w, b2.w);
    ring_lemmas::lemma_mul_congruence_right::<T>(a.z, b1.x, b2.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(b1.y), a.w.mul(b2.y), a.x.mul(b1.z), a.x.mul(b2.z),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(b1.y).sub(a.x.mul(b1.z)), a.w.mul(b2.y).sub(a.x.mul(b2.z)),
        a.y.mul(b1.w), a.y.mul(b2.w),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(b1.y).sub(a.x.mul(b1.z)).add(a.y.mul(b1.w)),
        a.w.mul(b2.y).sub(a.x.mul(b2.z)).add(a.y.mul(b2.w)),
        a.z.mul(b1.x), a.z.mul(b2.x),
    );

    // z component
    ring_lemmas::lemma_mul_congruence_right::<T>(a.w, b1.z, b2.z);
    ring_lemmas::lemma_mul_congruence_right::<T>(a.x, b1.y, b2.y);
    ring_lemmas::lemma_mul_congruence_right::<T>(a.y, b1.x, b2.x);
    ring_lemmas::lemma_mul_congruence_right::<T>(a.z, b1.w, b2.w);
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(b1.z), a.w.mul(b2.z), a.x.mul(b1.y), a.x.mul(b2.y),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(b1.z).add(a.x.mul(b1.y)), a.w.mul(b2.z).add(a.x.mul(b2.y)),
        a.y.mul(b1.x), a.y.mul(b2.x),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(b1.z).add(a.x.mul(b1.y)).sub(a.y.mul(b1.x)),
        a.w.mul(b2.z).add(a.x.mul(b2.y)).sub(a.y.mul(b2.x)),
        a.z.mul(b1.w), a.z.mul(b2.w),
    );
}

// ===========================================================================
// Mul distributivity lemmas
// ===========================================================================

/// Helper: rearrange w-component pattern for distributivity
/// (A+A')-(B+B')-(C+C')-(D+D') ≡ (A-B-C-D)+(A'-B'-C'-D')
pub proof fn lemma_rearrange_ssss<T: Ring>(
    a: T, ap: T, b: T, bp: T, c: T, cp: T, d: T, dp: T,
)
    ensures
        a.add(ap).sub(b.add(bp)).sub(c.add(cp)).sub(d.add(dp)).eqv(
            a.sub(b).sub(c).sub(d).add(ap.sub(bp).sub(cp).sub(dp))
        ),
{
    // Step 1: (A+A')-(B+B') ≡ (A-B)+(A'-B')
    lemma_sub_add_rearrange::<T>(a, ap, b, bp);
    // Step 2: Apply step 1, then rearrange again with (C+C')
    T::axiom_eqv_reflexive(c.add(cp));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.add(ap).sub(b.add(bp)), a.sub(b).add(ap.sub(bp)),
        c.add(cp), c.add(cp),
    );
    lemma_sub_add_rearrange::<T>(a.sub(b), ap.sub(bp), c, cp);
    T::axiom_eqv_transitive(
        a.add(ap).sub(b.add(bp)).sub(c.add(cp)),
        a.sub(b).add(ap.sub(bp)).sub(c.add(cp)),
        a.sub(b).sub(c).add(ap.sub(bp).sub(cp)),
    );
    // Step 3: Rearrange again with (D+D')
    T::axiom_eqv_reflexive(d.add(dp));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.add(ap).sub(b.add(bp)).sub(c.add(cp)),
        a.sub(b).sub(c).add(ap.sub(bp).sub(cp)),
        d.add(dp), d.add(dp),
    );
    lemma_sub_add_rearrange::<T>(a.sub(b).sub(c), ap.sub(bp).sub(cp), d, dp);
    T::axiom_eqv_transitive(
        a.add(ap).sub(b.add(bp)).sub(c.add(cp)).sub(d.add(dp)),
        a.sub(b).sub(c).add(ap.sub(bp).sub(cp)).sub(d.add(dp)),
        a.sub(b).sub(c).sub(d).add(ap.sub(bp).sub(cp).sub(dp)),
    );
}

/// Helper: rearrange x-component pattern (add-add-sub)
/// (A+A')+(B+B')+(C+C')-(D+D') ≡ (A+B+C-D)+(A'+B'+C'-D')
pub proof fn lemma_rearrange_aas<T: Ring>(
    a: T, ap: T, b: T, bp: T, c: T, cp: T, d: T, dp: T,
)
    ensures
        a.add(ap).add(b.add(bp)).add(c.add(cp)).sub(d.add(dp)).eqv(
            a.add(b).add(c).sub(d).add(ap.add(bp).add(cp).sub(dp))
        ),
{
    // Step 1: (A+A')+(B+B') ≡ (A+B)+(A'+B')
    lemma_add_add_rearrange::<T>(a, ap, b, bp);
    // Step 2: +(C+C')
    T::axiom_eqv_reflexive(c.add(cp));
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(ap).add(b.add(bp)), a.add(b).add(ap.add(bp)),
        c.add(cp), c.add(cp),
    );
    lemma_add_add_rearrange::<T>(a.add(b), ap.add(bp), c, cp);
    T::axiom_eqv_transitive(
        a.add(ap).add(b.add(bp)).add(c.add(cp)),
        a.add(b).add(ap.add(bp)).add(c.add(cp)),
        a.add(b).add(c).add(ap.add(bp).add(cp)),
    );
    // Step 3: -(D+D')
    T::axiom_eqv_reflexive(d.add(dp));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.add(ap).add(b.add(bp)).add(c.add(cp)),
        a.add(b).add(c).add(ap.add(bp).add(cp)),
        d.add(dp), d.add(dp),
    );
    lemma_sub_add_rearrange::<T>(a.add(b).add(c), ap.add(bp).add(cp), d, dp);
    T::axiom_eqv_transitive(
        a.add(ap).add(b.add(bp)).add(c.add(cp)).sub(d.add(dp)),
        a.add(b).add(c).add(ap.add(bp).add(cp)).sub(d.add(dp)),
        a.add(b).add(c).sub(d).add(ap.add(bp).add(cp).sub(dp)),
    );
}

/// Helper: rearrange y-component pattern (sub-add-add)
/// (A+A')-(B+B')+(C+C')+(D+D') ≡ (A-B+C+D)+(A'-B'+C'+D')
pub proof fn lemma_rearrange_saa<T: Ring>(
    a: T, ap: T, b: T, bp: T, c: T, cp: T, d: T, dp: T,
)
    ensures
        a.add(ap).sub(b.add(bp)).add(c.add(cp)).add(d.add(dp)).eqv(
            a.sub(b).add(c).add(d).add(ap.sub(bp).add(cp).add(dp))
        ),
{
    // Step 1: (A+A')-(B+B') ≡ (A-B)+(A'-B')
    lemma_sub_add_rearrange::<T>(a, ap, b, bp);
    // Step 2: +(C+C')
    T::axiom_eqv_reflexive(c.add(cp));
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(ap).sub(b.add(bp)), a.sub(b).add(ap.sub(bp)),
        c.add(cp), c.add(cp),
    );
    lemma_add_add_rearrange::<T>(a.sub(b), ap.sub(bp), c, cp);
    T::axiom_eqv_transitive(
        a.add(ap).sub(b.add(bp)).add(c.add(cp)),
        a.sub(b).add(ap.sub(bp)).add(c.add(cp)),
        a.sub(b).add(c).add(ap.sub(bp).add(cp)),
    );
    // Step 3: +(D+D')
    T::axiom_eqv_reflexive(d.add(dp));
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(ap).sub(b.add(bp)).add(c.add(cp)),
        a.sub(b).add(c).add(ap.sub(bp).add(cp)),
        d.add(dp), d.add(dp),
    );
    lemma_add_add_rearrange::<T>(a.sub(b).add(c), ap.sub(bp).add(cp), d, dp);
    T::axiom_eqv_transitive(
        a.add(ap).sub(b.add(bp)).add(c.add(cp)).add(d.add(dp)),
        a.sub(b).add(c).add(ap.sub(bp).add(cp)).add(d.add(dp)),
        a.sub(b).add(c).add(d).add(ap.sub(bp).add(cp).add(dp)),
    );
}

/// Helper: rearrange z-component pattern (add-sub-add)
/// (A+A')+(B+B')-(C+C')+(D+D') ≡ (A+B-C+D)+(A'+B'-C'+D')
pub proof fn lemma_rearrange_asa<T: Ring>(
    a: T, ap: T, b: T, bp: T, c: T, cp: T, d: T, dp: T,
)
    ensures
        a.add(ap).add(b.add(bp)).sub(c.add(cp)).add(d.add(dp)).eqv(
            a.add(b).sub(c).add(d).add(ap.add(bp).sub(cp).add(dp))
        ),
{
    // Step 1: (A+A')+(B+B') ≡ (A+B)+(A'+B')
    lemma_add_add_rearrange::<T>(a, ap, b, bp);
    // Step 2: -(C+C')
    T::axiom_eqv_reflexive(c.add(cp));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.add(ap).add(b.add(bp)), a.add(b).add(ap.add(bp)),
        c.add(cp), c.add(cp),
    );
    lemma_sub_add_rearrange::<T>(a.add(b), ap.add(bp), c, cp);
    T::axiom_eqv_transitive(
        a.add(ap).add(b.add(bp)).sub(c.add(cp)),
        a.add(b).add(ap.add(bp)).sub(c.add(cp)),
        a.add(b).sub(c).add(ap.add(bp).sub(cp)),
    );
    // Step 3: +(D+D')
    T::axiom_eqv_reflexive(d.add(dp));
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.add(ap).add(b.add(bp)).sub(c.add(cp)),
        a.add(b).sub(c).add(ap.add(bp).sub(cp)),
        d.add(dp), d.add(dp),
    );
    lemma_add_add_rearrange::<T>(a.add(b).sub(c), ap.add(bp).sub(cp), d, dp);
    T::axiom_eqv_transitive(
        a.add(ap).add(b.add(bp)).sub(c.add(cp)).add(d.add(dp)),
        a.add(b).sub(c).add(ap.add(bp).sub(cp)).add(d.add(dp)),
        a.add(b).sub(c).add(d).add(ap.add(bp).sub(cp).add(dp)),
    );
}

/// mul(a + b, c) ≡ mul(a, c) + mul(b, c)
pub proof fn lemma_mul_distributes_left<T: Ring>(a: Quat<T>, b: Quat<T>, c: Quat<T>)
    ensures
        mul(a.add(b), c).eqv(mul(a, c).add(mul(b, c))),
{
    // Distribution: (a_i+b_i)*c_j ≡ a_i*c_j + b_i*c_j
    ring_lemmas::lemma_mul_distributes_right::<T>(a.w, b.w, c.w);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.x, b.x, c.x);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.y, b.y, c.y);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.z, b.z, c.z);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.w, b.w, c.x);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.x, b.x, c.w);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.y, b.y, c.z);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.z, b.z, c.y);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.w, b.w, c.y);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.x, b.x, c.z);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.y, b.y, c.w);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.z, b.z, c.x);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.w, b.w, c.z);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.x, b.x, c.y);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.y, b.y, c.x);
    ring_lemmas::lemma_mul_distributes_right::<T>(a.z, b.z, c.w);

    // w: (aw+bw)*cw - (ax+bx)*cx - (ay+by)*cy - (az+bz)*cz
    // After dist: (Aw+Bw)-(Ax+Bx)-(Ay+By)-(Az+Bz) ≡ (Aw-Ax-Ay-Az)+(Bw-Bx-By-Bz)
    // First apply congruence to replace each distributed product
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.add(b.w).mul(c.w), a.w.mul(c.w).add(b.w.mul(c.w)),
        a.x.add(b.x).mul(c.x), a.x.mul(c.x).add(b.x.mul(c.x)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.add(b.w).mul(c.w).sub(a.x.add(b.x).mul(c.x)),
        a.w.mul(c.w).add(b.w.mul(c.w)).sub(a.x.mul(c.x).add(b.x.mul(c.x))),
        a.y.add(b.y).mul(c.y), a.y.mul(c.y).add(b.y.mul(c.y)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.add(b.w).mul(c.w).sub(a.x.add(b.x).mul(c.x)).sub(a.y.add(b.y).mul(c.y)),
        a.w.mul(c.w).add(b.w.mul(c.w)).sub(a.x.mul(c.x).add(b.x.mul(c.x))).sub(a.y.mul(c.y).add(b.y.mul(c.y))),
        a.z.add(b.z).mul(c.z), a.z.mul(c.z).add(b.z.mul(c.z)),
    );
    // Now rearrange
    lemma_rearrange_ssss::<T>(
        a.w.mul(c.w), b.w.mul(c.w), a.x.mul(c.x), b.x.mul(c.x),
        a.y.mul(c.y), b.y.mul(c.y), a.z.mul(c.z), b.z.mul(c.z),
    );
    T::axiom_eqv_transitive(
        mul(a.add(b), c).w,
        a.w.mul(c.w).add(b.w.mul(c.w)).sub(a.x.mul(c.x).add(b.x.mul(c.x))).sub(a.y.mul(c.y).add(b.y.mul(c.y))).sub(a.z.mul(c.z).add(b.z.mul(c.z))),
        mul(a, c).w.add(mul(b, c).w),
    );

    // x: (aw+bw)*cx + (ax+bx)*cw + (ay+by)*cz - (az+bz)*cy
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.add(b.w).mul(c.x), a.w.mul(c.x).add(b.w.mul(c.x)),
        a.x.add(b.x).mul(c.w), a.x.mul(c.w).add(b.x.mul(c.w)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.add(b.w).mul(c.x).add(a.x.add(b.x).mul(c.w)),
        a.w.mul(c.x).add(b.w.mul(c.x)).add(a.x.mul(c.w).add(b.x.mul(c.w))),
        a.y.add(b.y).mul(c.z), a.y.mul(c.z).add(b.y.mul(c.z)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.add(b.w).mul(c.x).add(a.x.add(b.x).mul(c.w)).add(a.y.add(b.y).mul(c.z)),
        a.w.mul(c.x).add(b.w.mul(c.x)).add(a.x.mul(c.w).add(b.x.mul(c.w))).add(a.y.mul(c.z).add(b.y.mul(c.z))),
        a.z.add(b.z).mul(c.y), a.z.mul(c.y).add(b.z.mul(c.y)),
    );
    lemma_rearrange_aas::<T>(
        a.w.mul(c.x), b.w.mul(c.x), a.x.mul(c.w), b.x.mul(c.w),
        a.y.mul(c.z), b.y.mul(c.z), a.z.mul(c.y), b.z.mul(c.y),
    );
    T::axiom_eqv_transitive(
        mul(a.add(b), c).x,
        a.w.mul(c.x).add(b.w.mul(c.x)).add(a.x.mul(c.w).add(b.x.mul(c.w))).add(a.y.mul(c.z).add(b.y.mul(c.z))).sub(a.z.mul(c.y).add(b.z.mul(c.y))),
        mul(a, c).x.add(mul(b, c).x),
    );

    // y: (aw+bw)*cy - (ax+bx)*cz + (ay+by)*cw + (az+bz)*cx
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.add(b.w).mul(c.y), a.w.mul(c.y).add(b.w.mul(c.y)),
        a.x.add(b.x).mul(c.z), a.x.mul(c.z).add(b.x.mul(c.z)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.add(b.w).mul(c.y).sub(a.x.add(b.x).mul(c.z)),
        a.w.mul(c.y).add(b.w.mul(c.y)).sub(a.x.mul(c.z).add(b.x.mul(c.z))),
        a.y.add(b.y).mul(c.w), a.y.mul(c.w).add(b.y.mul(c.w)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.add(b.w).mul(c.y).sub(a.x.add(b.x).mul(c.z)).add(a.y.add(b.y).mul(c.w)),
        a.w.mul(c.y).add(b.w.mul(c.y)).sub(a.x.mul(c.z).add(b.x.mul(c.z))).add(a.y.mul(c.w).add(b.y.mul(c.w))),
        a.z.add(b.z).mul(c.x), a.z.mul(c.x).add(b.z.mul(c.x)),
    );
    lemma_rearrange_saa::<T>(
        a.w.mul(c.y), b.w.mul(c.y), a.x.mul(c.z), b.x.mul(c.z),
        a.y.mul(c.w), b.y.mul(c.w), a.z.mul(c.x), b.z.mul(c.x),
    );
    T::axiom_eqv_transitive(
        mul(a.add(b), c).y,
        a.w.mul(c.y).add(b.w.mul(c.y)).sub(a.x.mul(c.z).add(b.x.mul(c.z))).add(a.y.mul(c.w).add(b.y.mul(c.w))).add(a.z.mul(c.x).add(b.z.mul(c.x))),
        mul(a, c).y.add(mul(b, c).y),
    );

    // z: (aw+bw)*cz + (ax+bx)*cy - (ay+by)*cx + (az+bz)*cw
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.add(b.w).mul(c.z), a.w.mul(c.z).add(b.w.mul(c.z)),
        a.x.add(b.x).mul(c.y), a.x.mul(c.y).add(b.x.mul(c.y)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.add(b.w).mul(c.z).add(a.x.add(b.x).mul(c.y)),
        a.w.mul(c.z).add(b.w.mul(c.z)).add(a.x.mul(c.y).add(b.x.mul(c.y))),
        a.y.add(b.y).mul(c.x), a.y.mul(c.x).add(b.y.mul(c.x)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.add(b.w).mul(c.z).add(a.x.add(b.x).mul(c.y)).sub(a.y.add(b.y).mul(c.x)),
        a.w.mul(c.z).add(b.w.mul(c.z)).add(a.x.mul(c.y).add(b.x.mul(c.y))).sub(a.y.mul(c.x).add(b.y.mul(c.x))),
        a.z.add(b.z).mul(c.w), a.z.mul(c.w).add(b.z.mul(c.w)),
    );
    lemma_rearrange_asa::<T>(
        a.w.mul(c.z), b.w.mul(c.z), a.x.mul(c.y), b.x.mul(c.y),
        a.y.mul(c.x), b.y.mul(c.x), a.z.mul(c.w), b.z.mul(c.w),
    );
    T::axiom_eqv_transitive(
        mul(a.add(b), c).z,
        a.w.mul(c.z).add(b.w.mul(c.z)).add(a.x.mul(c.y).add(b.x.mul(c.y))).sub(a.y.mul(c.x).add(b.y.mul(c.x))).add(a.z.mul(c.w).add(b.z.mul(c.w))),
        mul(a, c).z.add(mul(b, c).z),
    );
}

/// mul(a, b + c) ≡ mul(a, b) + mul(a, c)
pub proof fn lemma_mul_distributes_right<T: Ring>(a: Quat<T>, b: Quat<T>, c: Quat<T>)
    ensures
        mul(a, b.add(c)).eqv(mul(a, b).add(mul(a, c))),
{
    // Distribution: a_i*(b_j+c_j) ≡ a_i*b_j + a_i*c_j
    T::axiom_mul_distributes_left(a.w, b.w, c.w);
    T::axiom_mul_distributes_left(a.x, b.x, c.x);
    T::axiom_mul_distributes_left(a.y, b.y, c.y);
    T::axiom_mul_distributes_left(a.z, b.z, c.z);
    T::axiom_mul_distributes_left(a.w, b.x, c.x);
    T::axiom_mul_distributes_left(a.x, b.w, c.w);
    T::axiom_mul_distributes_left(a.y, b.z, c.z);
    T::axiom_mul_distributes_left(a.z, b.y, c.y);
    T::axiom_mul_distributes_left(a.w, b.y, c.y);
    T::axiom_mul_distributes_left(a.x, b.z, c.z);
    T::axiom_mul_distributes_left(a.y, b.w, c.w);
    T::axiom_mul_distributes_left(a.z, b.x, c.x);
    T::axiom_mul_distributes_left(a.w, b.z, c.z);
    T::axiom_mul_distributes_left(a.x, b.y, c.y);
    T::axiom_mul_distributes_left(a.y, b.x, c.x);
    T::axiom_mul_distributes_left(a.z, b.w, c.w);

    // w component: same structure as distributes_left
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(b.w.add(c.w)), a.w.mul(b.w).add(a.w.mul(c.w)),
        a.x.mul(b.x.add(c.x)), a.x.mul(b.x).add(a.x.mul(c.x)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(b.w.add(c.w)).sub(a.x.mul(b.x.add(c.x))),
        a.w.mul(b.w).add(a.w.mul(c.w)).sub(a.x.mul(b.x).add(a.x.mul(c.x))),
        a.y.mul(b.y.add(c.y)), a.y.mul(b.y).add(a.y.mul(c.y)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(b.w.add(c.w)).sub(a.x.mul(b.x.add(c.x))).sub(a.y.mul(b.y.add(c.y))),
        a.w.mul(b.w).add(a.w.mul(c.w)).sub(a.x.mul(b.x).add(a.x.mul(c.x))).sub(a.y.mul(b.y).add(a.y.mul(c.y))),
        a.z.mul(b.z.add(c.z)), a.z.mul(b.z).add(a.z.mul(c.z)),
    );
    lemma_rearrange_ssss::<T>(
        a.w.mul(b.w), a.w.mul(c.w), a.x.mul(b.x), a.x.mul(c.x),
        a.y.mul(b.y), a.y.mul(c.y), a.z.mul(b.z), a.z.mul(c.z),
    );
    T::axiom_eqv_transitive(
        mul(a, b.add(c)).w,
        a.w.mul(b.w).add(a.w.mul(c.w)).sub(a.x.mul(b.x).add(a.x.mul(c.x))).sub(a.y.mul(b.y).add(a.y.mul(c.y))).sub(a.z.mul(b.z).add(a.z.mul(c.z))),
        mul(a, b).w.add(mul(a, c).w),
    );

    // x component
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(b.x.add(c.x)), a.w.mul(b.x).add(a.w.mul(c.x)),
        a.x.mul(b.w.add(c.w)), a.x.mul(b.w).add(a.x.mul(c.w)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(b.x.add(c.x)).add(a.x.mul(b.w.add(c.w))),
        a.w.mul(b.x).add(a.w.mul(c.x)).add(a.x.mul(b.w).add(a.x.mul(c.w))),
        a.y.mul(b.z.add(c.z)), a.y.mul(b.z).add(a.y.mul(c.z)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(b.x.add(c.x)).add(a.x.mul(b.w.add(c.w))).add(a.y.mul(b.z.add(c.z))),
        a.w.mul(b.x).add(a.w.mul(c.x)).add(a.x.mul(b.w).add(a.x.mul(c.w))).add(a.y.mul(b.z).add(a.y.mul(c.z))),
        a.z.mul(b.y.add(c.y)), a.z.mul(b.y).add(a.z.mul(c.y)),
    );
    lemma_rearrange_aas::<T>(
        a.w.mul(b.x), a.w.mul(c.x), a.x.mul(b.w), a.x.mul(c.w),
        a.y.mul(b.z), a.y.mul(c.z), a.z.mul(b.y), a.z.mul(c.y),
    );
    T::axiom_eqv_transitive(
        mul(a, b.add(c)).x,
        a.w.mul(b.x).add(a.w.mul(c.x)).add(a.x.mul(b.w).add(a.x.mul(c.w))).add(a.y.mul(b.z).add(a.y.mul(c.z))).sub(a.z.mul(b.y).add(a.z.mul(c.y))),
        mul(a, b).x.add(mul(a, c).x),
    );

    // y component
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(b.y.add(c.y)), a.w.mul(b.y).add(a.w.mul(c.y)),
        a.x.mul(b.z.add(c.z)), a.x.mul(b.z).add(a.x.mul(c.z)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(b.y.add(c.y)).sub(a.x.mul(b.z.add(c.z))),
        a.w.mul(b.y).add(a.w.mul(c.y)).sub(a.x.mul(b.z).add(a.x.mul(c.z))),
        a.y.mul(b.w.add(c.w)), a.y.mul(b.w).add(a.y.mul(c.w)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(b.y.add(c.y)).sub(a.x.mul(b.z.add(c.z))).add(a.y.mul(b.w.add(c.w))),
        a.w.mul(b.y).add(a.w.mul(c.y)).sub(a.x.mul(b.z).add(a.x.mul(c.z))).add(a.y.mul(b.w).add(a.y.mul(c.w))),
        a.z.mul(b.x.add(c.x)), a.z.mul(b.x).add(a.z.mul(c.x)),
    );
    lemma_rearrange_saa::<T>(
        a.w.mul(b.y), a.w.mul(c.y), a.x.mul(b.z), a.x.mul(c.z),
        a.y.mul(b.w), a.y.mul(c.w), a.z.mul(b.x), a.z.mul(c.x),
    );
    T::axiom_eqv_transitive(
        mul(a, b.add(c)).y,
        a.w.mul(b.y).add(a.w.mul(c.y)).sub(a.x.mul(b.z).add(a.x.mul(c.z))).add(a.y.mul(b.w).add(a.y.mul(c.w))).add(a.z.mul(b.x).add(a.z.mul(c.x))),
        mul(a, b).y.add(mul(a, c).y),
    );

    // z component
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(b.z.add(c.z)), a.w.mul(b.z).add(a.w.mul(c.z)),
        a.x.mul(b.y.add(c.y)), a.x.mul(b.y).add(a.x.mul(c.y)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(b.z.add(c.z)).add(a.x.mul(b.y.add(c.y))),
        a.w.mul(b.z).add(a.w.mul(c.z)).add(a.x.mul(b.y).add(a.x.mul(c.y))),
        a.y.mul(b.x.add(c.x)), a.y.mul(b.x).add(a.y.mul(c.x)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(b.z.add(c.z)).add(a.x.mul(b.y.add(c.y))).sub(a.y.mul(b.x.add(c.x))),
        a.w.mul(b.z).add(a.w.mul(c.z)).add(a.x.mul(b.y).add(a.x.mul(c.y))).sub(a.y.mul(b.x).add(a.y.mul(c.x))),
        a.z.mul(b.w.add(c.w)), a.z.mul(b.w).add(a.z.mul(c.w)),
    );
    lemma_rearrange_asa::<T>(
        a.w.mul(b.z), a.w.mul(c.z), a.x.mul(b.y), a.x.mul(c.y),
        a.y.mul(b.x), a.y.mul(c.x), a.z.mul(b.w), a.z.mul(c.w),
    );
    T::axiom_eqv_transitive(
        mul(a, b.add(c)).z,
        a.w.mul(b.z).add(a.w.mul(c.z)).add(a.x.mul(b.y).add(a.x.mul(c.y))).sub(a.y.mul(b.x).add(a.y.mul(c.x))).add(a.z.mul(b.w).add(a.z.mul(c.w))),
        mul(a, b).z.add(mul(a, c).z),
    );
}

// ===========================================================================
// Mul-scale interaction lemmas
// ===========================================================================

/// Helper: factor s out of sub-sub-sub pattern
/// s*a - s*b - s*c - s*d ≡ s*(a - b - c - d)
pub proof fn lemma_factor_ssss<T: Ring>(s: T, a: T, b: T, c: T, d: T)
    ensures
        s.mul(a).sub(s.mul(b)).sub(s.mul(c)).sub(s.mul(d)).eqv(
            s.mul(a.sub(b).sub(c).sub(d))
        ),
{
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a, b);
    T::axiom_eqv_symmetric(s.mul(a.sub(b)), s.mul(a).sub(s.mul(b)));
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.sub(b), c);
    T::axiom_eqv_symmetric(s.mul(a.sub(b).sub(c)), s.mul(a.sub(b)).sub(s.mul(c)));
    T::axiom_eqv_reflexive(s.mul(c));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(a).sub(s.mul(b)), s.mul(a.sub(b)), s.mul(c), s.mul(c),
    );
    T::axiom_eqv_transitive(
        s.mul(a).sub(s.mul(b)).sub(s.mul(c)),
        s.mul(a.sub(b)).sub(s.mul(c)),
        s.mul(a.sub(b).sub(c)),
    );
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.sub(b).sub(c), d);
    T::axiom_eqv_symmetric(s.mul(a.sub(b).sub(c).sub(d)), s.mul(a.sub(b).sub(c)).sub(s.mul(d)));
    T::axiom_eqv_reflexive(s.mul(d));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(a).sub(s.mul(b)).sub(s.mul(c)), s.mul(a.sub(b).sub(c)), s.mul(d), s.mul(d),
    );
    T::axiom_eqv_transitive(
        s.mul(a).sub(s.mul(b)).sub(s.mul(c)).sub(s.mul(d)),
        s.mul(a.sub(b).sub(c)).sub(s.mul(d)),
        s.mul(a.sub(b).sub(c).sub(d)),
    );
}

/// Helper: factor s out of add-add-sub pattern
/// s*a + s*b + s*c - s*d ≡ s*(a + b + c - d)
pub proof fn lemma_factor_aas<T: Ring>(s: T, a: T, b: T, c: T, d: T)
    ensures
        s.mul(a).add(s.mul(b)).add(s.mul(c)).sub(s.mul(d)).eqv(
            s.mul(a.add(b).add(c).sub(d))
        ),
{
    T::axiom_mul_distributes_left(s, a, b);
    T::axiom_eqv_symmetric(s.mul(a.add(b)), s.mul(a).add(s.mul(b)));
    T::axiom_mul_distributes_left(s, a.add(b), c);
    T::axiom_eqv_symmetric(s.mul(a.add(b).add(c)), s.mul(a.add(b)).add(s.mul(c)));
    T::axiom_eqv_reflexive(s.mul(c));
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(a).add(s.mul(b)), s.mul(a.add(b)), s.mul(c), s.mul(c),
    );
    T::axiom_eqv_transitive(
        s.mul(a).add(s.mul(b)).add(s.mul(c)),
        s.mul(a.add(b)).add(s.mul(c)),
        s.mul(a.add(b).add(c)),
    );
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.add(b).add(c), d);
    T::axiom_eqv_symmetric(s.mul(a.add(b).add(c).sub(d)), s.mul(a.add(b).add(c)).sub(s.mul(d)));
    T::axiom_eqv_reflexive(s.mul(d));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(a).add(s.mul(b)).add(s.mul(c)), s.mul(a.add(b).add(c)), s.mul(d), s.mul(d),
    );
    T::axiom_eqv_transitive(
        s.mul(a).add(s.mul(b)).add(s.mul(c)).sub(s.mul(d)),
        s.mul(a.add(b).add(c)).sub(s.mul(d)),
        s.mul(a.add(b).add(c).sub(d)),
    );
}

/// Helper: factor s out of sub-add-add pattern
/// s*a - s*b + s*c + s*d ≡ s*(a - b + c + d)
pub proof fn lemma_factor_saa<T: Ring>(s: T, a: T, b: T, c: T, d: T)
    ensures
        s.mul(a).sub(s.mul(b)).add(s.mul(c)).add(s.mul(d)).eqv(
            s.mul(a.sub(b).add(c).add(d))
        ),
{
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a, b);
    T::axiom_eqv_symmetric(s.mul(a.sub(b)), s.mul(a).sub(s.mul(b)));
    T::axiom_mul_distributes_left(s, a.sub(b), c);
    T::axiom_eqv_symmetric(s.mul(a.sub(b).add(c)), s.mul(a.sub(b)).add(s.mul(c)));
    T::axiom_eqv_reflexive(s.mul(c));
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(a).sub(s.mul(b)), s.mul(a.sub(b)), s.mul(c), s.mul(c),
    );
    T::axiom_eqv_transitive(
        s.mul(a).sub(s.mul(b)).add(s.mul(c)),
        s.mul(a.sub(b)).add(s.mul(c)),
        s.mul(a.sub(b).add(c)),
    );
    T::axiom_mul_distributes_left(s, a.sub(b).add(c), d);
    T::axiom_eqv_symmetric(s.mul(a.sub(b).add(c).add(d)), s.mul(a.sub(b).add(c)).add(s.mul(d)));
    T::axiom_eqv_reflexive(s.mul(d));
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(a).sub(s.mul(b)).add(s.mul(c)), s.mul(a.sub(b).add(c)), s.mul(d), s.mul(d),
    );
    T::axiom_eqv_transitive(
        s.mul(a).sub(s.mul(b)).add(s.mul(c)).add(s.mul(d)),
        s.mul(a.sub(b).add(c)).add(s.mul(d)),
        s.mul(a.sub(b).add(c).add(d)),
    );
}

/// Helper: factor s out of add-sub-add pattern
/// s*a + s*b - s*c + s*d ≡ s*(a + b - c + d)
pub proof fn lemma_factor_asa<T: Ring>(s: T, a: T, b: T, c: T, d: T)
    ensures
        s.mul(a).add(s.mul(b)).sub(s.mul(c)).add(s.mul(d)).eqv(
            s.mul(a.add(b).sub(c).add(d))
        ),
{
    T::axiom_mul_distributes_left(s, a, b);
    T::axiom_eqv_symmetric(s.mul(a.add(b)), s.mul(a).add(s.mul(b)));
    ring_lemmas::lemma_mul_distributes_over_sub::<T>(s, a.add(b), c);
    T::axiom_eqv_symmetric(s.mul(a.add(b).sub(c)), s.mul(a.add(b)).sub(s.mul(c)));
    T::axiom_eqv_reflexive(s.mul(c));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(a).add(s.mul(b)), s.mul(a.add(b)), s.mul(c), s.mul(c),
    );
    T::axiom_eqv_transitive(
        s.mul(a).add(s.mul(b)).sub(s.mul(c)),
        s.mul(a.add(b)).sub(s.mul(c)),
        s.mul(a.add(b).sub(c)),
    );
    T::axiom_mul_distributes_left(s, a.add(b).sub(c), d);
    T::axiom_eqv_symmetric(s.mul(a.add(b).sub(c).add(d)), s.mul(a.add(b).sub(c)).add(s.mul(d)));
    T::axiom_eqv_reflexive(s.mul(d));
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(a).add(s.mul(b)).sub(s.mul(c)), s.mul(a.add(b).sub(c)), s.mul(d), s.mul(d),
    );
    T::axiom_eqv_transitive(
        s.mul(a).add(s.mul(b)).sub(s.mul(c)).add(s.mul(d)),
        s.mul(a.add(b).sub(c)).add(s.mul(d)),
        s.mul(a.add(b).sub(c).add(d)),
    );
}

/// mul(scale(s, a), b) ≡ scale(s, mul(a, b))
pub proof fn lemma_mul_scale_left<T: Ring>(s: T, a: Quat<T>, b: Quat<T>)
    ensures
        mul(scale(s, a), b).eqv(scale(s, mul(a, b))),
{
    // (s*ai)*bj ≡ s*(ai*bj) by associativity
    T::axiom_mul_associative(s, a.w, b.w); T::axiom_eqv_symmetric(s.mul(a.w).mul(b.w), s.mul(a.w.mul(b.w)));
    T::axiom_mul_associative(s, a.x, b.x); T::axiom_eqv_symmetric(s.mul(a.x).mul(b.x), s.mul(a.x.mul(b.x)));
    T::axiom_mul_associative(s, a.y, b.y); T::axiom_eqv_symmetric(s.mul(a.y).mul(b.y), s.mul(a.y.mul(b.y)));
    T::axiom_mul_associative(s, a.z, b.z); T::axiom_eqv_symmetric(s.mul(a.z).mul(b.z), s.mul(a.z.mul(b.z)));
    T::axiom_mul_associative(s, a.w, b.x); T::axiom_eqv_symmetric(s.mul(a.w).mul(b.x), s.mul(a.w.mul(b.x)));
    T::axiom_mul_associative(s, a.x, b.w); T::axiom_eqv_symmetric(s.mul(a.x).mul(b.w), s.mul(a.x.mul(b.w)));
    T::axiom_mul_associative(s, a.y, b.z); T::axiom_eqv_symmetric(s.mul(a.y).mul(b.z), s.mul(a.y.mul(b.z)));
    T::axiom_mul_associative(s, a.z, b.y); T::axiom_eqv_symmetric(s.mul(a.z).mul(b.y), s.mul(a.z.mul(b.y)));
    T::axiom_mul_associative(s, a.w, b.y); T::axiom_eqv_symmetric(s.mul(a.w).mul(b.y), s.mul(a.w.mul(b.y)));
    T::axiom_mul_associative(s, a.x, b.z); T::axiom_eqv_symmetric(s.mul(a.x).mul(b.z), s.mul(a.x.mul(b.z)));
    T::axiom_mul_associative(s, a.y, b.w); T::axiom_eqv_symmetric(s.mul(a.y).mul(b.w), s.mul(a.y.mul(b.w)));
    T::axiom_mul_associative(s, a.z, b.x); T::axiom_eqv_symmetric(s.mul(a.z).mul(b.x), s.mul(a.z.mul(b.x)));
    T::axiom_mul_associative(s, a.w, b.z); T::axiom_eqv_symmetric(s.mul(a.w).mul(b.z), s.mul(a.w.mul(b.z)));
    T::axiom_mul_associative(s, a.x, b.y); T::axiom_eqv_symmetric(s.mul(a.x).mul(b.y), s.mul(a.x.mul(b.y)));
    T::axiom_mul_associative(s, a.y, b.x); T::axiom_eqv_symmetric(s.mul(a.y).mul(b.x), s.mul(a.y.mul(b.x)));
    T::axiom_mul_associative(s, a.z, b.w); T::axiom_eqv_symmetric(s.mul(a.z).mul(b.w), s.mul(a.z.mul(b.w)));

    // w: (s*aw)*bw - (s*ax)*bx - (s*ay)*by - (s*az)*bz
    // ≡ s*(aw*bw) - s*(ax*bx) - s*(ay*by) - s*(az*bz)  [by congruence from assoc]
    // ≡ s*(aw*bw - ax*bx - ay*by - az*bz)              [by factoring]
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(a.w).mul(b.w), s.mul(a.w.mul(b.w)),
        s.mul(a.x).mul(b.x), s.mul(a.x.mul(b.x)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(a.w).mul(b.w).sub(s.mul(a.x).mul(b.x)),
        s.mul(a.w.mul(b.w)).sub(s.mul(a.x.mul(b.x))),
        s.mul(a.y).mul(b.y), s.mul(a.y.mul(b.y)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(a.w).mul(b.w).sub(s.mul(a.x).mul(b.x)).sub(s.mul(a.y).mul(b.y)),
        s.mul(a.w.mul(b.w)).sub(s.mul(a.x.mul(b.x))).sub(s.mul(a.y.mul(b.y))),
        s.mul(a.z).mul(b.z), s.mul(a.z.mul(b.z)),
    );
    lemma_factor_ssss::<T>(s, a.w.mul(b.w), a.x.mul(b.x), a.y.mul(b.y), a.z.mul(b.z));
    T::axiom_eqv_transitive(
        mul(scale(s, a), b).w,
        s.mul(a.w.mul(b.w)).sub(s.mul(a.x.mul(b.x))).sub(s.mul(a.y.mul(b.y))).sub(s.mul(a.z.mul(b.z))),
        scale(s, mul(a, b)).w,
    );

    // x: (s*aw)*bx + (s*ax)*bw + (s*ay)*bz - (s*az)*by
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(a.w).mul(b.x), s.mul(a.w.mul(b.x)),
        s.mul(a.x).mul(b.w), s.mul(a.x.mul(b.w)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(a.w).mul(b.x).add(s.mul(a.x).mul(b.w)),
        s.mul(a.w.mul(b.x)).add(s.mul(a.x.mul(b.w))),
        s.mul(a.y).mul(b.z), s.mul(a.y.mul(b.z)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(a.w).mul(b.x).add(s.mul(a.x).mul(b.w)).add(s.mul(a.y).mul(b.z)),
        s.mul(a.w.mul(b.x)).add(s.mul(a.x.mul(b.w))).add(s.mul(a.y.mul(b.z))),
        s.mul(a.z).mul(b.y), s.mul(a.z.mul(b.y)),
    );
    lemma_factor_aas::<T>(s, a.w.mul(b.x), a.x.mul(b.w), a.y.mul(b.z), a.z.mul(b.y));
    T::axiom_eqv_transitive(
        mul(scale(s, a), b).x,
        s.mul(a.w.mul(b.x)).add(s.mul(a.x.mul(b.w))).add(s.mul(a.y.mul(b.z))).sub(s.mul(a.z.mul(b.y))),
        scale(s, mul(a, b)).x,
    );

    // y: (s*aw)*by - (s*ax)*bz + (s*ay)*bw + (s*az)*bx
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(a.w).mul(b.y), s.mul(a.w.mul(b.y)),
        s.mul(a.x).mul(b.z), s.mul(a.x.mul(b.z)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(a.w).mul(b.y).sub(s.mul(a.x).mul(b.z)),
        s.mul(a.w.mul(b.y)).sub(s.mul(a.x.mul(b.z))),
        s.mul(a.y).mul(b.w), s.mul(a.y.mul(b.w)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(a.w).mul(b.y).sub(s.mul(a.x).mul(b.z)).add(s.mul(a.y).mul(b.w)),
        s.mul(a.w.mul(b.y)).sub(s.mul(a.x.mul(b.z))).add(s.mul(a.y.mul(b.w))),
        s.mul(a.z).mul(b.x), s.mul(a.z.mul(b.x)),
    );
    lemma_factor_saa::<T>(s, a.w.mul(b.y), a.x.mul(b.z), a.y.mul(b.w), a.z.mul(b.x));
    T::axiom_eqv_transitive(
        mul(scale(s, a), b).y,
        s.mul(a.w.mul(b.y)).sub(s.mul(a.x.mul(b.z))).add(s.mul(a.y.mul(b.w))).add(s.mul(a.z.mul(b.x))),
        scale(s, mul(a, b)).y,
    );

    // z: (s*aw)*bz + (s*ax)*by - (s*ay)*bx + (s*az)*bw
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(a.w).mul(b.z), s.mul(a.w.mul(b.z)),
        s.mul(a.x).mul(b.y), s.mul(a.x.mul(b.y)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(a.w).mul(b.z).add(s.mul(a.x).mul(b.y)),
        s.mul(a.w.mul(b.z)).add(s.mul(a.x.mul(b.y))),
        s.mul(a.y).mul(b.x), s.mul(a.y.mul(b.x)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(a.w).mul(b.z).add(s.mul(a.x).mul(b.y)).sub(s.mul(a.y).mul(b.x)),
        s.mul(a.w.mul(b.z)).add(s.mul(a.x.mul(b.y))).sub(s.mul(a.y.mul(b.x))),
        s.mul(a.z).mul(b.w), s.mul(a.z.mul(b.w)),
    );
    lemma_factor_asa::<T>(s, a.w.mul(b.z), a.x.mul(b.y), a.y.mul(b.x), a.z.mul(b.w));
    T::axiom_eqv_transitive(
        mul(scale(s, a), b).z,
        s.mul(a.w.mul(b.z)).add(s.mul(a.x.mul(b.y))).sub(s.mul(a.y.mul(b.x))).add(s.mul(a.z.mul(b.w))),
        scale(s, mul(a, b)).z,
    );
}

/// mul(a, scale(s, b)) ≡ scale(s, mul(a, b))
pub proof fn lemma_mul_scale_right<T: Ring>(a: Quat<T>, s: T, b: Quat<T>)
    ensures
        mul(a, scale(s, b)).eqv(scale(s, mul(a, b))),
{
    // ai*(s*bj) ≡ s*(ai*bj) via: ai*(s*bj) = (ai*s)*bj = (s*ai)*bj = s*(ai*bj)
    // For each of the 16 product pairs, establish ai.mul(s.mul(bj)).eqv(s.mul(ai.mul(bj)))

    // Macro pattern: assoc_back, comm, congruence, assoc_forward, chain
    // ai*(s*bj) ≡ (ai*s)*bj  [assoc reversed]
    // (ai*s)*bj ≡ (s*ai)*bj  [comm on ai*s]
    // (s*ai)*bj ≡ s*(ai*bj)  [assoc]
    // Chain all three

    // w,w
    T::axiom_mul_associative(a.w, s, b.w); T::axiom_eqv_symmetric(a.w.mul(s).mul(b.w), a.w.mul(s.mul(b.w)));
    T::axiom_mul_commutative(a.w, s); T::axiom_mul_congruence_left(a.w.mul(s), s.mul(a.w), b.w);
    T::axiom_mul_associative(s, a.w, b.w);
    T::axiom_eqv_transitive(a.w.mul(s.mul(b.w)), a.w.mul(s).mul(b.w), s.mul(a.w).mul(b.w));
    T::axiom_eqv_transitive(a.w.mul(s.mul(b.w)), s.mul(a.w).mul(b.w), s.mul(a.w.mul(b.w)));
    // x,x
    T::axiom_mul_associative(a.x, s, b.x); T::axiom_eqv_symmetric(a.x.mul(s).mul(b.x), a.x.mul(s.mul(b.x)));
    T::axiom_mul_commutative(a.x, s); T::axiom_mul_congruence_left(a.x.mul(s), s.mul(a.x), b.x);
    T::axiom_mul_associative(s, a.x, b.x);
    T::axiom_eqv_transitive(a.x.mul(s.mul(b.x)), a.x.mul(s).mul(b.x), s.mul(a.x).mul(b.x));
    T::axiom_eqv_transitive(a.x.mul(s.mul(b.x)), s.mul(a.x).mul(b.x), s.mul(a.x.mul(b.x)));
    // y,y
    T::axiom_mul_associative(a.y, s, b.y); T::axiom_eqv_symmetric(a.y.mul(s).mul(b.y), a.y.mul(s.mul(b.y)));
    T::axiom_mul_commutative(a.y, s); T::axiom_mul_congruence_left(a.y.mul(s), s.mul(a.y), b.y);
    T::axiom_mul_associative(s, a.y, b.y);
    T::axiom_eqv_transitive(a.y.mul(s.mul(b.y)), a.y.mul(s).mul(b.y), s.mul(a.y).mul(b.y));
    T::axiom_eqv_transitive(a.y.mul(s.mul(b.y)), s.mul(a.y).mul(b.y), s.mul(a.y.mul(b.y)));
    // z,z
    T::axiom_mul_associative(a.z, s, b.z); T::axiom_eqv_symmetric(a.z.mul(s).mul(b.z), a.z.mul(s.mul(b.z)));
    T::axiom_mul_commutative(a.z, s); T::axiom_mul_congruence_left(a.z.mul(s), s.mul(a.z), b.z);
    T::axiom_mul_associative(s, a.z, b.z);
    T::axiom_eqv_transitive(a.z.mul(s.mul(b.z)), a.z.mul(s).mul(b.z), s.mul(a.z).mul(b.z));
    T::axiom_eqv_transitive(a.z.mul(s.mul(b.z)), s.mul(a.z).mul(b.z), s.mul(a.z.mul(b.z)));
    // w,x
    T::axiom_mul_associative(a.w, s, b.x); T::axiom_eqv_symmetric(a.w.mul(s).mul(b.x), a.w.mul(s.mul(b.x)));
    T::axiom_mul_congruence_left(a.w.mul(s), s.mul(a.w), b.x);
    T::axiom_mul_associative(s, a.w, b.x);
    T::axiom_eqv_transitive(a.w.mul(s.mul(b.x)), a.w.mul(s).mul(b.x), s.mul(a.w).mul(b.x));
    T::axiom_eqv_transitive(a.w.mul(s.mul(b.x)), s.mul(a.w).mul(b.x), s.mul(a.w.mul(b.x)));
    // x,w
    T::axiom_mul_associative(a.x, s, b.w); T::axiom_eqv_symmetric(a.x.mul(s).mul(b.w), a.x.mul(s.mul(b.w)));
    T::axiom_mul_congruence_left(a.x.mul(s), s.mul(a.x), b.w);
    T::axiom_mul_associative(s, a.x, b.w);
    T::axiom_eqv_transitive(a.x.mul(s.mul(b.w)), a.x.mul(s).mul(b.w), s.mul(a.x).mul(b.w));
    T::axiom_eqv_transitive(a.x.mul(s.mul(b.w)), s.mul(a.x).mul(b.w), s.mul(a.x.mul(b.w)));
    // y,z
    T::axiom_mul_associative(a.y, s, b.z); T::axiom_eqv_symmetric(a.y.mul(s).mul(b.z), a.y.mul(s.mul(b.z)));
    T::axiom_mul_congruence_left(a.y.mul(s), s.mul(a.y), b.z);
    T::axiom_mul_associative(s, a.y, b.z);
    T::axiom_eqv_transitive(a.y.mul(s.mul(b.z)), a.y.mul(s).mul(b.z), s.mul(a.y).mul(b.z));
    T::axiom_eqv_transitive(a.y.mul(s.mul(b.z)), s.mul(a.y).mul(b.z), s.mul(a.y.mul(b.z)));
    // z,y
    T::axiom_mul_associative(a.z, s, b.y); T::axiom_eqv_symmetric(a.z.mul(s).mul(b.y), a.z.mul(s.mul(b.y)));
    T::axiom_mul_congruence_left(a.z.mul(s), s.mul(a.z), b.y);
    T::axiom_mul_associative(s, a.z, b.y);
    T::axiom_eqv_transitive(a.z.mul(s.mul(b.y)), a.z.mul(s).mul(b.y), s.mul(a.z).mul(b.y));
    T::axiom_eqv_transitive(a.z.mul(s.mul(b.y)), s.mul(a.z).mul(b.y), s.mul(a.z.mul(b.y)));
    // w,y
    T::axiom_mul_associative(a.w, s, b.y); T::axiom_eqv_symmetric(a.w.mul(s).mul(b.y), a.w.mul(s.mul(b.y)));
    T::axiom_mul_congruence_left(a.w.mul(s), s.mul(a.w), b.y);
    T::axiom_mul_associative(s, a.w, b.y);
    T::axiom_eqv_transitive(a.w.mul(s.mul(b.y)), a.w.mul(s).mul(b.y), s.mul(a.w).mul(b.y));
    T::axiom_eqv_transitive(a.w.mul(s.mul(b.y)), s.mul(a.w).mul(b.y), s.mul(a.w.mul(b.y)));
    // x,z
    T::axiom_mul_associative(a.x, s, b.z); T::axiom_eqv_symmetric(a.x.mul(s).mul(b.z), a.x.mul(s.mul(b.z)));
    T::axiom_mul_congruence_left(a.x.mul(s), s.mul(a.x), b.z);
    T::axiom_mul_associative(s, a.x, b.z);
    T::axiom_eqv_transitive(a.x.mul(s.mul(b.z)), a.x.mul(s).mul(b.z), s.mul(a.x).mul(b.z));
    T::axiom_eqv_transitive(a.x.mul(s.mul(b.z)), s.mul(a.x).mul(b.z), s.mul(a.x.mul(b.z)));
    // y,w
    T::axiom_mul_associative(a.y, s, b.w); T::axiom_eqv_symmetric(a.y.mul(s).mul(b.w), a.y.mul(s.mul(b.w)));
    T::axiom_mul_congruence_left(a.y.mul(s), s.mul(a.y), b.w);
    T::axiom_mul_associative(s, a.y, b.w);
    T::axiom_eqv_transitive(a.y.mul(s.mul(b.w)), a.y.mul(s).mul(b.w), s.mul(a.y).mul(b.w));
    T::axiom_eqv_transitive(a.y.mul(s.mul(b.w)), s.mul(a.y).mul(b.w), s.mul(a.y.mul(b.w)));
    // z,x
    T::axiom_mul_associative(a.z, s, b.x); T::axiom_eqv_symmetric(a.z.mul(s).mul(b.x), a.z.mul(s.mul(b.x)));
    T::axiom_mul_congruence_left(a.z.mul(s), s.mul(a.z), b.x);
    T::axiom_mul_associative(s, a.z, b.x);
    T::axiom_eqv_transitive(a.z.mul(s.mul(b.x)), a.z.mul(s).mul(b.x), s.mul(a.z).mul(b.x));
    T::axiom_eqv_transitive(a.z.mul(s.mul(b.x)), s.mul(a.z).mul(b.x), s.mul(a.z.mul(b.x)));
    // w,z
    T::axiom_mul_associative(a.w, s, b.z); T::axiom_eqv_symmetric(a.w.mul(s).mul(b.z), a.w.mul(s.mul(b.z)));
    T::axiom_mul_congruence_left(a.w.mul(s), s.mul(a.w), b.z);
    T::axiom_mul_associative(s, a.w, b.z);
    T::axiom_eqv_transitive(a.w.mul(s.mul(b.z)), a.w.mul(s).mul(b.z), s.mul(a.w).mul(b.z));
    T::axiom_eqv_transitive(a.w.mul(s.mul(b.z)), s.mul(a.w).mul(b.z), s.mul(a.w.mul(b.z)));
    // x,y
    T::axiom_mul_associative(a.x, s, b.y); T::axiom_eqv_symmetric(a.x.mul(s).mul(b.y), a.x.mul(s.mul(b.y)));
    T::axiom_mul_congruence_left(a.x.mul(s), s.mul(a.x), b.y);
    T::axiom_mul_associative(s, a.x, b.y);
    T::axiom_eqv_transitive(a.x.mul(s.mul(b.y)), a.x.mul(s).mul(b.y), s.mul(a.x).mul(b.y));
    T::axiom_eqv_transitive(a.x.mul(s.mul(b.y)), s.mul(a.x).mul(b.y), s.mul(a.x.mul(b.y)));
    // y,x
    T::axiom_mul_associative(a.y, s, b.x); T::axiom_eqv_symmetric(a.y.mul(s).mul(b.x), a.y.mul(s.mul(b.x)));
    T::axiom_mul_congruence_left(a.y.mul(s), s.mul(a.y), b.x);
    T::axiom_mul_associative(s, a.y, b.x);
    T::axiom_eqv_transitive(a.y.mul(s.mul(b.x)), a.y.mul(s).mul(b.x), s.mul(a.y).mul(b.x));
    T::axiom_eqv_transitive(a.y.mul(s.mul(b.x)), s.mul(a.y).mul(b.x), s.mul(a.y.mul(b.x)));
    // z,w
    T::axiom_mul_associative(a.z, s, b.w); T::axiom_eqv_symmetric(a.z.mul(s).mul(b.w), a.z.mul(s.mul(b.w)));
    T::axiom_mul_congruence_left(a.z.mul(s), s.mul(a.z), b.w);
    T::axiom_mul_associative(s, a.z, b.w);
    T::axiom_eqv_transitive(a.z.mul(s.mul(b.w)), a.z.mul(s).mul(b.w), s.mul(a.z).mul(b.w));
    T::axiom_eqv_transitive(a.z.mul(s.mul(b.w)), s.mul(a.z).mul(b.w), s.mul(a.z.mul(b.w)));

    // Now for each component, substitute and factor (same structure as mul_scale_left)
    // w
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(s.mul(b.w)), s.mul(a.w.mul(b.w)),
        a.x.mul(s.mul(b.x)), s.mul(a.x.mul(b.x)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(s.mul(b.w)).sub(a.x.mul(s.mul(b.x))),
        s.mul(a.w.mul(b.w)).sub(s.mul(a.x.mul(b.x))),
        a.y.mul(s.mul(b.y)), s.mul(a.y.mul(b.y)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(s.mul(b.w)).sub(a.x.mul(s.mul(b.x))).sub(a.y.mul(s.mul(b.y))),
        s.mul(a.w.mul(b.w)).sub(s.mul(a.x.mul(b.x))).sub(s.mul(a.y.mul(b.y))),
        a.z.mul(s.mul(b.z)), s.mul(a.z.mul(b.z)),
    );
    lemma_factor_ssss::<T>(s, a.w.mul(b.w), a.x.mul(b.x), a.y.mul(b.y), a.z.mul(b.z));
    T::axiom_eqv_transitive(
        mul(a, scale(s, b)).w,
        s.mul(a.w.mul(b.w)).sub(s.mul(a.x.mul(b.x))).sub(s.mul(a.y.mul(b.y))).sub(s.mul(a.z.mul(b.z))),
        scale(s, mul(a, b)).w,
    );

    // x
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(s.mul(b.x)), s.mul(a.w.mul(b.x)),
        a.x.mul(s.mul(b.w)), s.mul(a.x.mul(b.w)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(s.mul(b.x)).add(a.x.mul(s.mul(b.w))),
        s.mul(a.w.mul(b.x)).add(s.mul(a.x.mul(b.w))),
        a.y.mul(s.mul(b.z)), s.mul(a.y.mul(b.z)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(s.mul(b.x)).add(a.x.mul(s.mul(b.w))).add(a.y.mul(s.mul(b.z))),
        s.mul(a.w.mul(b.x)).add(s.mul(a.x.mul(b.w))).add(s.mul(a.y.mul(b.z))),
        a.z.mul(s.mul(b.y)), s.mul(a.z.mul(b.y)),
    );
    lemma_factor_aas::<T>(s, a.w.mul(b.x), a.x.mul(b.w), a.y.mul(b.z), a.z.mul(b.y));
    T::axiom_eqv_transitive(
        mul(a, scale(s, b)).x,
        s.mul(a.w.mul(b.x)).add(s.mul(a.x.mul(b.w))).add(s.mul(a.y.mul(b.z))).sub(s.mul(a.z.mul(b.y))),
        scale(s, mul(a, b)).x,
    );

    // y
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(s.mul(b.y)), s.mul(a.w.mul(b.y)),
        a.x.mul(s.mul(b.z)), s.mul(a.x.mul(b.z)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(s.mul(b.y)).sub(a.x.mul(s.mul(b.z))),
        s.mul(a.w.mul(b.y)).sub(s.mul(a.x.mul(b.z))),
        a.y.mul(s.mul(b.w)), s.mul(a.y.mul(b.w)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(s.mul(b.y)).sub(a.x.mul(s.mul(b.z))).add(a.y.mul(s.mul(b.w))),
        s.mul(a.w.mul(b.y)).sub(s.mul(a.x.mul(b.z))).add(s.mul(a.y.mul(b.w))),
        a.z.mul(s.mul(b.x)), s.mul(a.z.mul(b.x)),
    );
    lemma_factor_saa::<T>(s, a.w.mul(b.y), a.x.mul(b.z), a.y.mul(b.w), a.z.mul(b.x));
    T::axiom_eqv_transitive(
        mul(a, scale(s, b)).y,
        s.mul(a.w.mul(b.y)).sub(s.mul(a.x.mul(b.z))).add(s.mul(a.y.mul(b.w))).add(s.mul(a.z.mul(b.x))),
        scale(s, mul(a, b)).y,
    );

    // z
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(s.mul(b.z)), s.mul(a.w.mul(b.z)),
        a.x.mul(s.mul(b.y)), s.mul(a.x.mul(b.y)),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.w.mul(s.mul(b.z)).add(a.x.mul(s.mul(b.y))),
        s.mul(a.w.mul(b.z)).add(s.mul(a.x.mul(b.y))),
        a.y.mul(s.mul(b.x)), s.mul(a.y.mul(b.x)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(s.mul(b.z)).add(a.x.mul(s.mul(b.y))).sub(a.y.mul(s.mul(b.x))),
        s.mul(a.w.mul(b.z)).add(s.mul(a.x.mul(b.y))).sub(s.mul(a.y.mul(b.x))),
        a.z.mul(s.mul(b.w)), s.mul(a.z.mul(b.w)),
    );
    lemma_factor_asa::<T>(s, a.w.mul(b.z), a.x.mul(b.y), a.y.mul(b.x), a.z.mul(b.w));
    T::axiom_eqv_transitive(
        mul(a, scale(s, b)).z,
        s.mul(a.w.mul(b.z)).add(s.mul(a.x.mul(b.y))).sub(s.mul(a.y.mul(b.x))).add(s.mul(a.z.mul(b.w))),
        scale(s, mul(a, b)).z,
    );
}

} // verus!
