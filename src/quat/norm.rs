use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use super::Quat;
#[allow(unused_imports)]
use super::ops::*;
#[allow(unused_imports)]
use super::ops::mul;
use super::conjugate::*;
use super::assoc::lemma_mul_associative;

verus! {

// ===========================================================================
// Spec functions
// ===========================================================================

/// Real quaternion: (t, 0, 0, 0)
pub open spec fn real<T: Ring>(t: T) -> Quat<T> {
    Quat { w: t, x: T::zero(), y: T::zero(), z: T::zero() }
}

// ===========================================================================
// Norm congruence
// ===========================================================================

/// norm_sq preserves equivalence
pub proof fn lemma_norm_sq_congruence<T: Ring>(a: Quat<T>, b: Quat<T>)
    requires a.eqv(b),
    ensures norm_sq(a).eqv(norm_sq(b)),
{
    // a.w*a.w ≡ b.w*b.w, etc.
    ring_lemmas::lemma_mul_congruence::<T>(a.w, b.w, a.w, b.w);
    ring_lemmas::lemma_mul_congruence::<T>(a.x, b.x, a.x, b.x);
    ring_lemmas::lemma_mul_congruence::<T>(a.y, b.y, a.y, b.y);
    ring_lemmas::lemma_mul_congruence::<T>(a.z, b.z, a.z, b.z);
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(a.w), b.w.mul(b.w),
        a.x.mul(a.x), b.x.mul(b.x),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(a.w).add(a.x.mul(a.x)), b.w.mul(b.w).add(b.x.mul(b.x)),
        a.y.mul(a.y), b.y.mul(b.y),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.w.mul(a.w).add(a.x.mul(a.x)).add(a.y.mul(a.y)),
        b.w.mul(b.w).add(b.x.mul(b.x)).add(b.y.mul(b.y)),
        a.z.mul(a.z), b.z.mul(b.z),
    );
}

// ===========================================================================
// Real quaternion helpers
// ===========================================================================

/// mul(q, real(s)) ≡ scale(s, q)
pub proof fn lemma_mul_real_right<T: Ring>(q: Quat<T>, s: T)
    ensures mul(q, real(s)).eqv(scale(s, q)),
{
    let z = T::zero();
    // Establish zero products
    T::axiom_mul_zero_right(q.w);
    T::axiom_mul_zero_right(q.x);
    T::axiom_mul_zero_right(q.y);
    T::axiom_mul_zero_right(q.z);

    // w: q.w*s - q.x*0 - q.y*0 - q.z*0 ≡ q.w*s - 0 - 0 - 0 ≡ q.w*s
    // But scale(s, q).w = s*q.w, and q.w*s ≡ s*q.w by commutativity
    T::axiom_mul_commutative(q.w, s);
    T::axiom_mul_commutative(q.x, s);
    T::axiom_mul_commutative(q.y, s);
    T::axiom_mul_commutative(q.z, s);
    T::axiom_eqv_reflexive(z);

    // w: q.w*s - q.x*0 - q.y*0 - q.z*0
    additive_group_lemmas::lemma_sub_congruence::<T>(q.w.mul(s), s.mul(q.w), q.x.mul(z), z);
    lemma_sub_zero::<T>(s.mul(q.w));
    T::axiom_eqv_transitive(q.w.mul(s).sub(q.x.mul(z)), s.mul(q.w).sub(z), s.mul(q.w));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        q.w.mul(s).sub(q.x.mul(z)), s.mul(q.w), q.y.mul(z), z,
    );
    lemma_sub_zero::<T>(s.mul(q.w));
    T::axiom_eqv_transitive(
        q.w.mul(s).sub(q.x.mul(z)).sub(q.y.mul(z)), s.mul(q.w).sub(z), s.mul(q.w),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        q.w.mul(s).sub(q.x.mul(z)).sub(q.y.mul(z)), s.mul(q.w), q.z.mul(z), z,
    );
    lemma_sub_zero::<T>(s.mul(q.w));
    T::axiom_eqv_transitive(
        mul(q, real(s)).w, s.mul(q.w).sub(z), s.mul(q.w),
    );

    // x: q.w*0 + q.x*s + q.y*0 - q.z*0
    additive_group_lemmas::lemma_add_congruence::<T>(q.w.mul(z), z, q.x.mul(s), s.mul(q.x));
    additive_group_lemmas::lemma_add_zero_left::<T>(s.mul(q.x));
    T::axiom_eqv_transitive(q.w.mul(z).add(q.x.mul(s)), z.add(s.mul(q.x)), s.mul(q.x));
    additive_group_lemmas::lemma_add_congruence::<T>(
        q.w.mul(z).add(q.x.mul(s)), s.mul(q.x), q.y.mul(z), z,
    );
    T::axiom_add_zero_right(s.mul(q.x));
    T::axiom_eqv_transitive(
        q.w.mul(z).add(q.x.mul(s)).add(q.y.mul(z)), s.mul(q.x).add(z), s.mul(q.x),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        q.w.mul(z).add(q.x.mul(s)).add(q.y.mul(z)), s.mul(q.x), q.z.mul(z), z,
    );
    lemma_sub_zero::<T>(s.mul(q.x));
    T::axiom_eqv_transitive(
        mul(q, real(s)).x, s.mul(q.x).sub(z), s.mul(q.x),
    );

    // y: q.w*0 - q.x*0 + q.y*s + q.z*0
    additive_group_lemmas::lemma_sub_congruence::<T>(q.w.mul(z), z, q.x.mul(z), z);
    additive_group_lemmas::lemma_sub_self::<T>(z);
    T::axiom_eqv_transitive(q.w.mul(z).sub(q.x.mul(z)), z.sub(z), z);
    additive_group_lemmas::lemma_add_congruence::<T>(
        q.w.mul(z).sub(q.x.mul(z)), z, q.y.mul(s), s.mul(q.y),
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(s.mul(q.y));
    T::axiom_eqv_transitive(
        q.w.mul(z).sub(q.x.mul(z)).add(q.y.mul(s)), z.add(s.mul(q.y)), s.mul(q.y),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        q.w.mul(z).sub(q.x.mul(z)).add(q.y.mul(s)), s.mul(q.y), q.z.mul(z), z,
    );
    T::axiom_add_zero_right(s.mul(q.y));
    T::axiom_eqv_transitive(
        mul(q, real(s)).y, s.mul(q.y).add(z), s.mul(q.y),
    );

    // z: q.w*0 + q.x*0 - q.y*0 + q.z*s
    additive_group_lemmas::lemma_add_congruence::<T>(q.w.mul(z), z, q.x.mul(z), z);
    T::axiom_add_zero_right(z);
    T::axiom_eqv_transitive(q.w.mul(z).add(q.x.mul(z)), z.add(z), z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        q.w.mul(z).add(q.x.mul(z)), z, q.y.mul(z), z,
    );
    additive_group_lemmas::lemma_sub_self::<T>(z);
    T::axiom_eqv_transitive(q.w.mul(z).add(q.x.mul(z)).sub(q.y.mul(z)), z.sub(z), z);
    additive_group_lemmas::lemma_add_congruence::<T>(
        q.w.mul(z).add(q.x.mul(z)).sub(q.y.mul(z)), z, q.z.mul(s), s.mul(q.z),
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(s.mul(q.z));
    T::axiom_eqv_transitive(
        mul(q, real(s)).z, z.add(s.mul(q.z)), s.mul(q.z),
    );
}

/// mul(real(s), q) ≡ scale(s, q)
pub proof fn lemma_mul_real_left<T: Ring>(s: T, q: Quat<T>)
    ensures mul(real(s), q).eqv(scale(s, q)),
{
    let z = T::zero();
    ring_lemmas::lemma_mul_zero_left::<T>(q.w);
    ring_lemmas::lemma_mul_zero_left::<T>(q.x);
    ring_lemmas::lemma_mul_zero_left::<T>(q.y);
    ring_lemmas::lemma_mul_zero_left::<T>(q.z);
    T::axiom_eqv_reflexive(z);
    T::axiom_eqv_reflexive(s.mul(q.w));
    T::axiom_eqv_reflexive(s.mul(q.x));
    T::axiom_eqv_reflexive(s.mul(q.y));
    T::axiom_eqv_reflexive(s.mul(q.z));
    lemma_sub_zero::<T>(s.mul(q.w));
    lemma_sub_zero::<T>(s.mul(q.x));
    lemma_sub_zero::<T>(s.mul(q.y));
    lemma_sub_zero::<T>(s.mul(q.z));

    // w: s*qw - 0*qx - 0*qy - 0*qz ≡ s*qw - 0 - 0 - 0 ≡ s*qw
    additive_group_lemmas::lemma_sub_congruence::<T>(s.mul(q.w), s.mul(q.w), z.mul(q.x), z);
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(q.w).sub(z.mul(q.x)), s.mul(q.w).sub(z), z.mul(q.y), z,
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(q.w).sub(z.mul(q.x)).sub(z.mul(q.y)), s.mul(q.w).sub(z).sub(z), z.mul(q.z), z,
    );
    // s*qw.sub(z).sub(z).sub(z) ≡ s*qw
    additive_group_lemmas::lemma_sub_congruence::<T>(s.mul(q.w).sub(z), s.mul(q.w), z, z);
    T::axiom_eqv_transitive(s.mul(q.w).sub(z).sub(z), s.mul(q.w).sub(z), s.mul(q.w));
    additive_group_lemmas::lemma_sub_congruence::<T>(s.mul(q.w).sub(z).sub(z), s.mul(q.w), z, z);
    T::axiom_eqv_transitive(s.mul(q.w).sub(z).sub(z).sub(z), s.mul(q.w).sub(z), s.mul(q.w));
    T::axiom_eqv_transitive(mul(real::<T>(s), q).w, s.mul(q.w).sub(z).sub(z).sub(z), s.mul(q.w));

    // x: s*qx + 0*qw + 0*qz - 0*qy ≡ s*qx
    additive_group_lemmas::lemma_add_congruence::<T>(s.mul(q.x), s.mul(q.x), z.mul(q.w), z);
    T::axiom_add_zero_right(s.mul(q.x));
    T::axiom_eqv_transitive(s.mul(q.x).add(z.mul(q.w)), s.mul(q.x).add(z), s.mul(q.x));
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(q.x).add(z.mul(q.w)), s.mul(q.x), z.mul(q.z), z,
    );
    T::axiom_add_zero_right(s.mul(q.x));
    T::axiom_eqv_transitive(
        s.mul(q.x).add(z.mul(q.w)).add(z.mul(q.z)), s.mul(q.x).add(z), s.mul(q.x),
    );
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(q.x).add(z.mul(q.w)).add(z.mul(q.z)), s.mul(q.x), z.mul(q.y), z,
    );
    T::axiom_eqv_transitive(
        mul(real::<T>(s), q).x, s.mul(q.x).sub(z), s.mul(q.x),
    );

    // y: s*qy - 0*qz + 0*qw + 0*qx ≡ s*qy
    additive_group_lemmas::lemma_sub_congruence::<T>(s.mul(q.y), s.mul(q.y), z.mul(q.z), z);
    T::axiom_eqv_transitive(s.mul(q.y).sub(z.mul(q.z)), s.mul(q.y).sub(z), s.mul(q.y));
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(q.y).sub(z.mul(q.z)), s.mul(q.y), z.mul(q.w), z,
    );
    T::axiom_add_zero_right(s.mul(q.y));
    T::axiom_eqv_transitive(
        s.mul(q.y).sub(z.mul(q.z)).add(z.mul(q.w)), s.mul(q.y).add(z), s.mul(q.y),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(q.y).sub(z.mul(q.z)).add(z.mul(q.w)), s.mul(q.y), z.mul(q.x), z,
    );
    T::axiom_add_zero_right(s.mul(q.y));
    T::axiom_eqv_transitive(
        mul(real::<T>(s), q).y, s.mul(q.y).add(z), s.mul(q.y),
    );

    // z: s*qz + 0*qy - 0*qx + 0*qw ≡ s*qz
    additive_group_lemmas::lemma_add_congruence::<T>(s.mul(q.z), s.mul(q.z), z.mul(q.y), z);
    T::axiom_add_zero_right(s.mul(q.z));
    T::axiom_eqv_transitive(s.mul(q.z).add(z.mul(q.y)), s.mul(q.z).add(z), s.mul(q.z));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        s.mul(q.z).add(z.mul(q.y)), s.mul(q.z), z.mul(q.x), z,
    );
    T::axiom_eqv_transitive(s.mul(q.z).add(z.mul(q.y)).sub(z.mul(q.x)), s.mul(q.z).sub(z), s.mul(q.z));
    additive_group_lemmas::lemma_add_congruence::<T>(
        s.mul(q.z).add(z.mul(q.y)).sub(z.mul(q.x)), s.mul(q.z), z.mul(q.w), z,
    );
    T::axiom_add_zero_right(s.mul(q.z));
    T::axiom_eqv_transitive(
        mul(real::<T>(s), q).z, s.mul(q.z).add(z), s.mul(q.z),
    );
}

/// scale(k, real(s)) ≡ real(k.mul(s))
pub proof fn lemma_real_scale<T: Ring>(k: T, s: T)
    ensures scale(k, real(s)).eqv(real(k.mul(s))),
{
    T::axiom_eqv_reflexive(k.mul(s));
    T::axiom_mul_zero_right(k);
}

// ===========================================================================
// Mul-conjugate: q * conj(q) ≡ real(norm_sq(q))
// ===========================================================================

/// a*(-b) + b*a ≡ 0
/// Proof: a*(-b) ≡ -(a*b), b*a ≡ a*b [comm], so -(a*b) + a*b = 0
pub proof fn lemma_mul_neg_add_rev_zero<T: Ring>(a: T, b: T)
    ensures a.mul(b.neg()).add(b.mul(a)).eqv(T::zero()),
{
    ring_lemmas::lemma_mul_neg_right::<T>(a, b);
    T::axiom_eqv_reflexive(b.mul(a));
    additive_group_lemmas::lemma_add_congruence::<T>(
        a.mul(b.neg()), a.mul(b).neg(), b.mul(a), b.mul(a),
    );
    T::axiom_mul_commutative(b, a);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        a.mul(b).neg(), b.mul(a), a.mul(b),
    );
    additive_group_lemmas::lemma_add_inverse_left::<T>(a.mul(b));
    T::axiom_eqv_transitive(
        a.mul(b).neg().add(b.mul(a)),
        a.mul(b).neg().add(a.mul(b)),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        a.mul(b.neg()).add(b.mul(a)),
        a.mul(b).neg().add(b.mul(a)),
        T::zero(),
    );
}

/// c*(-d) - d*(-c) ≡ 0
/// Proof: c*(-d) ≡ -(c*d), -(d*(-c)) ≡ d*c ≡ c*d, so -(c*d) + c*d = 0
pub proof fn lemma_mul_neg_sub_rev_neg_zero<T: Ring>(c: T, d: T)
    ensures c.mul(d.neg()).sub(d.mul(c.neg())).eqv(T::zero()),
{
    // c*(-d) ≡ -(c*d)
    ring_lemmas::lemma_mul_neg_right::<T>(c, d);
    // d*(-c) ≡ -(d*c)
    ring_lemmas::lemma_mul_neg_right::<T>(d, c);
    // sub → add_neg: c*(-d) - d*(-c) ≡ c*(-d) + (-(d*(-c)))
    T::axiom_sub_is_add_neg(c.mul(d.neg()), d.mul(c.neg()));
    // -(d*(-c)) ≡ -(-(d*c)) ≡ d*c
    additive_group_lemmas::lemma_neg_congruence::<T>(d.mul(c.neg()), d.mul(c).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(d.mul(c));
    T::axiom_eqv_transitive(d.mul(c.neg()).neg(), d.mul(c).neg().neg(), d.mul(c));
    // c*(-d) + (-(d*(-c))) ≡ -(c*d) + d*c
    additive_group_lemmas::lemma_add_congruence::<T>(
        c.mul(d.neg()), c.mul(d).neg(),
        d.mul(c.neg()).neg(), d.mul(c),
    );
    // -(c*d) + d*c ≡ -(c*d) + c*d ≡ 0
    T::axiom_mul_commutative(d, c);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        c.mul(d).neg(), d.mul(c), c.mul(d),
    );
    additive_group_lemmas::lemma_add_inverse_left::<T>(c.mul(d));
    T::axiom_eqv_transitive(
        c.mul(d).neg().add(d.mul(c)),
        c.mul(d).neg().add(c.mul(d)),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        c.mul(d.neg()).add(d.mul(c.neg()).neg()),
        c.mul(d).neg().add(d.mul(c)),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        c.mul(d.neg()).sub(d.mul(c.neg())),
        c.mul(d.neg()).add(d.mul(c.neg()).neg()),
        T::zero(),
    );
}

/// W-component of mul(q, conj(q)):
/// q.w*q.w - q.x*(-q.x) - q.y*(-q.y) - q.z*(-q.z)
/// ≡ q.w*q.w + q.x*q.x + q.y*q.y + q.z*q.z = norm_sq(q)
///
/// Strategy: -a*(-b) ≡ -(a*(-b)) ≡ -(-(a*b)) ≡ a*b using neg chain,
/// so sub becomes add.
pub proof fn lemma_mul_conj_w<T: Ring>(q: Quat<T>)
    ensures mul(q, conjugate(q)).w.eqv(norm_sq(q)),
{
    let (w, x, y, z) = (q.w, q.x, q.y, q.z);
    // mul(q, conj(q)).w = w*w - x*(-x) - y*(-y) - z*(-z)
    // We need: a.sub(b.mul(b.neg())) ≡ a.add(b.mul(b))
    // Because b*(-b) ≡ -(b*b) by mul_neg_right
    // So -(b*(-b)) ≡ -(-(b*b)) ≡ b*b by neg_involution

    // x*(-x) ≡ -(x*x)
    ring_lemmas::lemma_mul_neg_right::<T>(x, x);
    // sub converts: w*w - x*(-x) = w*w + -(x*(-x))
    // -(x*(-x)) ≡ -(-(x*x)) ≡ x*x
    additive_group_lemmas::lemma_neg_congruence::<T>(x.mul(x.neg()), x.mul(x).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(x.mul(x));
    T::axiom_eqv_transitive(x.mul(x.neg()).neg(), x.mul(x).neg().neg(), x.mul(x));

    // Similarly for y and z
    ring_lemmas::lemma_mul_neg_right::<T>(y, y);
    additive_group_lemmas::lemma_neg_congruence::<T>(y.mul(y.neg()), y.mul(y).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(y.mul(y));
    T::axiom_eqv_transitive(y.mul(y.neg()).neg(), y.mul(y).neg().neg(), y.mul(y));

    ring_lemmas::lemma_mul_neg_right::<T>(z, z);
    additive_group_lemmas::lemma_neg_congruence::<T>(z.mul(z.neg()), z.mul(z).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(z.mul(z));
    T::axiom_eqv_transitive(z.mul(z.neg()).neg(), z.mul(z).neg().neg(), z.mul(z));

    // Now convert subs to adds:
    // w*w - x*(-x) = w*w + (-(x*(-x)))
    T::axiom_sub_is_add_neg(w.mul(w), x.mul(x.neg()));
    additive_group_lemmas::lemma_add_congruence_right::<T>(w.mul(w), x.mul(x.neg()).neg(), x.mul(x));
    T::axiom_eqv_transitive(
        w.mul(w).sub(x.mul(x.neg())),
        w.mul(w).add(x.mul(x.neg()).neg()),
        w.mul(w).add(x.mul(x)),
    );

    // (w*w + x*x) - y*(-y) ≡ (w*w + x*x) + y*y
    T::axiom_sub_is_add_neg(w.mul(w).add(x.mul(x)), y.mul(y.neg()));
    // But we need to connect from the LHS expression
    T::axiom_sub_is_add_neg(w.mul(w).sub(x.mul(x.neg())), y.mul(y.neg()));
    T::axiom_eqv_reflexive(y.mul(y.neg()));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        w.mul(w).sub(x.mul(x.neg())), w.mul(w).add(x.mul(x)),
        y.mul(y.neg()), y.mul(y.neg()),
    );
    // w*w.sub(x*(-x)).sub(y*(-y)) ≡ (w*w+x*x).sub(y*(-y))
    // = (w*w+x*x) + (-(y*(-y)))
    T::axiom_sub_is_add_neg(w.mul(w).add(x.mul(x)), y.mul(y.neg()));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        w.mul(w).add(x.mul(x)), y.mul(y.neg()).neg(), y.mul(y),
    );
    T::axiom_eqv_transitive(
        w.mul(w).add(x.mul(x)).sub(y.mul(y.neg())),
        w.mul(w).add(x.mul(x)).add(y.mul(y.neg()).neg()),
        w.mul(w).add(x.mul(x)).add(y.mul(y)),
    );
    T::axiom_eqv_transitive(
        w.mul(w).sub(x.mul(x.neg())).sub(y.mul(y.neg())),
        w.mul(w).add(x.mul(x)).sub(y.mul(y.neg())),
        w.mul(w).add(x.mul(x)).add(y.mul(y)),
    );

    // (w*w + x*x + y*y) - z*(-z) ≡ (w*w + x*x + y*y) + z*z = norm_sq
    T::axiom_eqv_reflexive(z.mul(z.neg()));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        w.mul(w).sub(x.mul(x.neg())).sub(y.mul(y.neg())),
        w.mul(w).add(x.mul(x)).add(y.mul(y)),
        z.mul(z.neg()), z.mul(z.neg()),
    );
    T::axiom_sub_is_add_neg(w.mul(w).add(x.mul(x)).add(y.mul(y)), z.mul(z.neg()));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        w.mul(w).add(x.mul(x)).add(y.mul(y)), z.mul(z.neg()).neg(), z.mul(z),
    );
    T::axiom_eqv_transitive(
        w.mul(w).add(x.mul(x)).add(y.mul(y)).sub(z.mul(z.neg())),
        w.mul(w).add(x.mul(x)).add(y.mul(y)).add(z.mul(z.neg()).neg()),
        w.mul(w).add(x.mul(x)).add(y.mul(y)).add(z.mul(z)),
    );
    T::axiom_eqv_transitive(
        mul(q, conjugate(q)).w,
        w.mul(w).add(x.mul(x)).add(y.mul(y)).sub(z.mul(z.neg())),
        norm_sq(q),
    );
}

/// X-component of mul(q, conj(q)) ≡ 0
/// q.w*(-q.x) + q.x*q.w + q.y*(-q.z) - q.z*(-q.y)
/// = -(q.w*q.x) + q.x*q.w + -(q.y*q.z) - (-(q.z*q.y))
/// The first two cancel by commutativity, the last two cancel similarly.
pub proof fn lemma_mul_conj_x<T: Ring>(q: Quat<T>)
    ensures mul(q, conjugate(q)).x.eqv(T::zero()),
{
    let (w, x, y, z) = (q.w, q.x, q.y, q.z);
    // mul(q, conj(q)).x = w*(-x) + x*w + y*(-z) - z*(-y)

    // Step 1: w*(-x) ≡ -(w*x)
    ring_lemmas::lemma_mul_neg_right::<T>(w, x);
    // Step 2: y*(-z) ≡ -(y*z)
    ring_lemmas::lemma_mul_neg_right::<T>(y, z);
    // Step 3: z*(-y) ≡ -(z*y)
    ring_lemmas::lemma_mul_neg_right::<T>(z, y);

    // Congruence to replace products:
    // w*(-x) + x*w ≡ -(w*x) + x*w
    T::axiom_eqv_reflexive(x.mul(w));
    additive_group_lemmas::lemma_add_congruence::<T>(
        w.mul(x.neg()), w.mul(x).neg(), x.mul(w), x.mul(w),
    );
    // -(w*x) + x*w ≡ -(w*x) + w*x [commutativity: x*w ≡ w*x]
    T::axiom_mul_commutative(x, w);
    T::axiom_eqv_reflexive(w.mul(x).neg());
    additive_group_lemmas::lemma_add_congruence::<T>(
        w.mul(x).neg(), w.mul(x).neg(), x.mul(w), w.mul(x),
    );
    // -(w*x) + w*x ≡ 0
    additive_group_lemmas::lemma_add_inverse_left::<T>(w.mul(x));
    T::axiom_eqv_transitive(
        w.mul(x).neg().add(x.mul(w)),
        w.mul(x).neg().add(w.mul(x)),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        w.mul(x.neg()).add(x.mul(w)),
        w.mul(x).neg().add(x.mul(w)),
        T::zero(),
    );

    // y*(-z) ≡ -(y*z)  (already established)
    // -(z*(-y)) ≡ -(-(z*y)) ≡ z*y  by neg_involution
    additive_group_lemmas::lemma_neg_congruence::<T>(z.mul(y.neg()), z.mul(y).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(z.mul(y));
    T::axiom_eqv_transitive(z.mul(y.neg()).neg(), z.mul(y).neg().neg(), z.mul(y));

    // Now: the full expression: (w*(-x) + x*w) + y*(-z) - z*(-y)
    // We've shown w*(-x) + x*w ≡ 0
    // Now add y*(-z): 0 + y*(-z) ≡ y*(-z) ≡ -(y*z)
    T::axiom_eqv_reflexive(y.mul(z.neg()));
    additive_group_lemmas::lemma_add_congruence::<T>(
        w.mul(x.neg()).add(x.mul(w)), T::zero(),
        y.mul(z.neg()), y.mul(z.neg()),
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(y.mul(z.neg()));
    T::axiom_eqv_transitive(
        w.mul(x.neg()).add(x.mul(w)).add(y.mul(z.neg())),
        T::zero().add(y.mul(z.neg())),
        y.mul(z.neg()),
    );
    // y*(-z) ≡ -(y*z)
    T::axiom_eqv_transitive(
        w.mul(x.neg()).add(x.mul(w)).add(y.mul(z.neg())),
        y.mul(z.neg()),
        y.mul(z).neg(),
    );

    // Sub z*(-y): -(y*z) - z*(-y) ≡ -(y*z) + (-(z*(-y)))
    // We showed -(z*(-y)) ≡ z*y
    // So: -(y*z) + z*y
    // By commutativity: z*y ≡ y*z
    // So: -(y*z) + y*z ≡ 0
    T::axiom_eqv_reflexive(z.mul(y.neg()));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        w.mul(x.neg()).add(x.mul(w)).add(y.mul(z.neg())),
        y.mul(z).neg(),
        z.mul(y.neg()), z.mul(y.neg()),
    );
    T::axiom_sub_is_add_neg(y.mul(z).neg(), z.mul(y.neg()));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        y.mul(z).neg(), z.mul(y.neg()).neg(), z.mul(y),
    );
    T::axiom_eqv_transitive(
        y.mul(z).neg().sub(z.mul(y.neg())),
        y.mul(z).neg().add(z.mul(y.neg()).neg()),
        y.mul(z).neg().add(z.mul(y)),
    );
    // z*y ≡ y*z by commutativity
    T::axiom_mul_commutative(z, y);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        y.mul(z).neg(), z.mul(y), y.mul(z),
    );
    additive_group_lemmas::lemma_add_inverse_left::<T>(y.mul(z));
    T::axiom_eqv_transitive(
        y.mul(z).neg().add(z.mul(y)),
        y.mul(z).neg().add(y.mul(z)),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        y.mul(z).neg().sub(z.mul(y.neg())),
        y.mul(z).neg().add(z.mul(y)),
        T::zero(),
    );

    // Final chain
    T::axiom_eqv_transitive(
        mul(q, conjugate(q)).x,
        y.mul(z).neg().sub(z.mul(y.neg())),
        T::zero(),
    );
}

/// a*b - b*a ≡ 0 (ring commutativity means commutator vanishes)
pub proof fn lemma_commutator_zero<T: Ring>(a: T, b: T)
    ensures a.mul(b).sub(b.mul(a)).eqv(T::zero()),
{
    T::axiom_mul_commutative(a, b);
    T::axiom_eqv_symmetric(a.mul(b), b.mul(a));
    T::axiom_eqv_reflexive(a.mul(b));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        a.mul(b), a.mul(b), b.mul(a), a.mul(b),
    );
    additive_group_lemmas::lemma_sub_self::<T>(a.mul(b));
    T::axiom_eqv_transitive(
        a.mul(b).sub(b.mul(a)),
        a.mul(b).sub(a.mul(b)),
        T::zero(),
    );
}

/// Y-component of mul(q, conj(q)) ≡ 0
/// q.w*(-q.y) - q.x*(-q.z) + q.y*q.w + q.z*(-q.x)
pub proof fn lemma_mul_conj_y<T: Ring>(q: Quat<T>)
    ensures mul(q, conjugate(q)).y.eqv(T::zero()),
{
    let (w, x, y, z) = (q.w, q.x, q.y, q.z);
    // mul(q, conj(q)).y = w*(-y) - x*(-z) + y*w + z*(-x)
    //
    // w*(-y) ≡ -(w*y), x*(-z) ≡ -(x*z), z*(-x) ≡ -(z*x)
    //
    // = -(w*y) - (-(x*z)) + y*w + -(z*x)
    // = -(w*y) + x*z + y*w + -(z*x)
    // = (-(w*y) + y*w) + (x*z + -(z*x))
    // = (-(w*y) + w*y) + (x*z - z*x)  [commutativity]
    // = 0 + 0 = 0

    ring_lemmas::lemma_mul_neg_right::<T>(w, y);
    ring_lemmas::lemma_mul_neg_right::<T>(x, z);
    ring_lemmas::lemma_mul_neg_right::<T>(z, x);

    // -(x*(-z)) ≡ -(-(x*z)) ≡ x*z
    additive_group_lemmas::lemma_neg_congruence::<T>(x.mul(z.neg()), x.mul(z).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(x.mul(z));
    T::axiom_eqv_transitive(x.mul(z.neg()).neg(), x.mul(z).neg().neg(), x.mul(z));

    // w*(-y) - x*(-z) = w*(-y) + (-(x*(-z)))
    T::axiom_sub_is_add_neg(w.mul(y.neg()), x.mul(z.neg()));
    additive_group_lemmas::lemma_add_congruence::<T>(
        w.mul(y.neg()), w.mul(y).neg(),
        x.mul(z.neg()).neg(), x.mul(z),
    );
    T::axiom_eqv_transitive(
        w.mul(y.neg()).sub(x.mul(z.neg())),
        w.mul(y.neg()).add(x.mul(z.neg()).neg()),
        w.mul(y).neg().add(x.mul(z)),
    );

    // + y*w: (-(w*y) + x*z) + y*w
    T::axiom_eqv_reflexive(y.mul(w));
    additive_group_lemmas::lemma_add_congruence::<T>(
        w.mul(y.neg()).sub(x.mul(z.neg())),
        w.mul(y).neg().add(x.mul(z)),
        y.mul(w), y.mul(w),
    );

    // Rearrange: (-(w*y) + x*z) + y*w ≡ (-(w*y) + y*w) + x*z
    // Use add assoc + commutativity
    T::axiom_add_associative(w.mul(y).neg(), x.mul(z), y.mul(w));
    T::axiom_eqv_symmetric(
        w.mul(y).neg().add(x.mul(z)).add(y.mul(w)),
        w.mul(y).neg().add(x.mul(z).add(y.mul(w))),
    );
    T::axiom_add_commutative(x.mul(z), y.mul(w));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        w.mul(y).neg(), x.mul(z).add(y.mul(w)), y.mul(w).add(x.mul(z)),
    );
    T::axiom_add_associative(w.mul(y).neg(), y.mul(w), x.mul(z));
    T::axiom_eqv_symmetric(
        w.mul(y).neg().add(y.mul(w)).add(x.mul(z)),
        w.mul(y).neg().add(y.mul(w).add(x.mul(z))),
    );
    T::axiom_eqv_transitive(
        w.mul(y).neg().add(x.mul(z).add(y.mul(w))),
        w.mul(y).neg().add(y.mul(w).add(x.mul(z))),
        w.mul(y).neg().add(y.mul(w)).add(x.mul(z)),
    );
    T::axiom_eqv_transitive(
        w.mul(y).neg().add(x.mul(z)).add(y.mul(w)),
        w.mul(y).neg().add(x.mul(z).add(y.mul(w))),
        w.mul(y).neg().add(y.mul(w)).add(x.mul(z)),
    );

    // -(w*y) + y*w ≡ -(w*y) + w*y ≡ 0
    T::axiom_mul_commutative(y, w);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        w.mul(y).neg(), y.mul(w), w.mul(y),
    );
    additive_group_lemmas::lemma_add_inverse_left::<T>(w.mul(y));
    T::axiom_eqv_transitive(
        w.mul(y).neg().add(y.mul(w)),
        w.mul(y).neg().add(w.mul(y)),
        T::zero(),
    );

    // So (-(w*y) + y*w) + x*z ≡ 0 + x*z ≡ x*z
    T::axiom_eqv_reflexive(x.mul(z));
    additive_group_lemmas::lemma_add_congruence::<T>(
        w.mul(y).neg().add(y.mul(w)), T::zero(),
        x.mul(z), x.mul(z),
    );
    additive_group_lemmas::lemma_add_zero_left::<T>(x.mul(z));
    T::axiom_eqv_transitive(
        w.mul(y).neg().add(y.mul(w)).add(x.mul(z)),
        T::zero().add(x.mul(z)),
        x.mul(z),
    );

    // Connect the chain back:
    // w*(-y).sub(x*(-z)).add(y*w) ≡ w*y.neg.add(x*z).add(y*w) ≡ -(wy)+yw + xz ≡ xz
    T::axiom_eqv_transitive(
        w.mul(y.neg()).sub(x.mul(z.neg())).add(y.mul(w)),
        w.mul(y).neg().add(x.mul(z)).add(y.mul(w)),
        w.mul(y).neg().add(y.mul(w)).add(x.mul(z)),
    );
    T::axiom_eqv_transitive(
        w.mul(y.neg()).sub(x.mul(z.neg())).add(y.mul(w)),
        w.mul(y).neg().add(y.mul(w)).add(x.mul(z)),
        x.mul(z),
    );

    // + z*(-x): x*z + z*(-x) ≡ x*z + -(z*x) ≡ x*z - z*x
    T::axiom_eqv_reflexive(z.mul(x.neg()));
    additive_group_lemmas::lemma_add_congruence::<T>(
        w.mul(y.neg()).sub(x.mul(z.neg())).add(y.mul(w)),
        x.mul(z),
        z.mul(x.neg()), z.mul(x.neg()),
    );
    // x*z + z*(-x) ≡ x*z + -(z*x)
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        x.mul(z), z.mul(x.neg()), z.mul(x).neg(),
    );
    // x*z + -(z*x) ≡ x*z - z*x  [sub_is_add_neg reverse]
    T::axiom_sub_is_add_neg(x.mul(z), z.mul(x));
    T::axiom_eqv_symmetric(x.mul(z).sub(z.mul(x)), x.mul(z).add(z.mul(x).neg()));
    T::axiom_eqv_transitive(
        x.mul(z).add(z.mul(x.neg())),
        x.mul(z).add(z.mul(x).neg()),
        x.mul(z).sub(z.mul(x)),
    );
    // x*z - z*x ≡ 0 by commutativity
    lemma_commutator_zero::<T>(x, z);
    T::axiom_eqv_transitive(
        x.mul(z).add(z.mul(x.neg())),
        x.mul(z).sub(z.mul(x)),
        T::zero(),
    );
    // Final chain
    T::axiom_eqv_transitive(
        w.mul(y.neg()).sub(x.mul(z.neg())).add(y.mul(w)).add(z.mul(x.neg())),
        x.mul(z).add(z.mul(x.neg())),
        T::zero(),
    );
}

/// Z-component of mul(q, conj(q)) ≡ 0
/// q.w*(-q.z) + q.x*(-q.y) - q.y*(-q.x) + q.z*q.w
pub proof fn lemma_mul_conj_z<T: Ring>(q: Quat<T>)
    ensures mul(q, conjugate(q)).z.eqv(T::zero()),
{
    let (w, x, y, z) = (q.w, q.x, q.y, q.z);
    // mul(q, conj(q)).z = w*(-z) + x*(-y) - y*(-x) + z*w
    //
    // w*(-z) ≡ -(w*z), x*(-y) ≡ -(x*y), y*(-x) ≡ -(y*x)
    //
    // = -(w*z) + -(x*y) - (-(y*x)) + z*w
    // = -(w*z) + -(x*y) + y*x + z*w
    // = (-(w*z) + z*w) + (-(x*y) + y*x)  [rearrange]
    // = 0 + 0 = 0

    ring_lemmas::lemma_mul_neg_right::<T>(w, z);
    ring_lemmas::lemma_mul_neg_right::<T>(x, y);
    ring_lemmas::lemma_mul_neg_right::<T>(y, x);

    // -(y*(-x)) ≡ -(-(y*x)) ≡ y*x
    additive_group_lemmas::lemma_neg_congruence::<T>(y.mul(x.neg()), y.mul(x).neg());
    additive_group_lemmas::lemma_neg_involution::<T>(y.mul(x));
    T::axiom_eqv_transitive(y.mul(x.neg()).neg(), y.mul(x).neg().neg(), y.mul(x));

    // w*(-z) + x*(-y) ≡ -(w*z) + -(x*y)
    additive_group_lemmas::lemma_add_congruence::<T>(
        w.mul(z.neg()), w.mul(z).neg(),
        x.mul(y.neg()), x.mul(y).neg(),
    );

    // - y*(-x): (-(w*z) + -(x*y)) - y*(-x)
    // = (-(w*z) + -(x*y)) + (-(y*(-x)))
    // ≡ (-(w*z) + -(x*y)) + y*x
    T::axiom_sub_is_add_neg(
        w.mul(z).neg().add(x.mul(y).neg()),
        y.mul(x.neg()),
    );
    // But we need to track from the original expression
    T::axiom_eqv_reflexive(y.mul(x.neg()));
    additive_group_lemmas::lemma_sub_congruence::<T>(
        w.mul(z.neg()).add(x.mul(y.neg())),
        w.mul(z).neg().add(x.mul(y).neg()),
        y.mul(x.neg()), y.mul(x.neg()),
    );
    T::axiom_sub_is_add_neg(
        w.mul(z.neg()).add(x.mul(y.neg())),
        y.mul(x.neg()),
    );
    T::axiom_sub_is_add_neg(
        w.mul(z).neg().add(x.mul(y).neg()),
        y.mul(x.neg()),
    );
    T::axiom_eqv_reflexive(w.mul(z).neg().add(x.mul(y).neg()));
    additive_group_lemmas::lemma_add_congruence::<T>(
        w.mul(z).neg().add(x.mul(y).neg()),
        w.mul(z).neg().add(x.mul(y).neg()),
        y.mul(x.neg()).neg(), y.mul(x),
    );
    T::axiom_eqv_transitive(
        w.mul(z).neg().add(x.mul(y).neg()).sub(y.mul(x.neg())),
        w.mul(z).neg().add(x.mul(y).neg()).add(y.mul(x.neg()).neg()),
        w.mul(z).neg().add(x.mul(y).neg()).add(y.mul(x)),
    );
    T::axiom_eqv_transitive(
        w.mul(z.neg()).add(x.mul(y.neg())).sub(y.mul(x.neg())),
        w.mul(z).neg().add(x.mul(y).neg()).sub(y.mul(x.neg())),
        w.mul(z).neg().add(x.mul(y).neg()).add(y.mul(x)),
    );

    // + z*w: (-(w*z) + -(x*y) + y*x) + z*w
    T::axiom_eqv_reflexive(z.mul(w));
    additive_group_lemmas::lemma_add_congruence::<T>(
        w.mul(z.neg()).add(x.mul(y.neg())).sub(y.mul(x.neg())),
        w.mul(z).neg().add(x.mul(y).neg()).add(y.mul(x)),
        z.mul(w), z.mul(w),
    );

    // Rearrange: (-(wz) + -(xy) + yx) + zw ≡ (-(wz) + zw) + (-(xy) + yx)
    // Use associativity and commutativity of add
    // (a + b + c) + d = a + (b + c) + d = a + (b + (c + d))
    //                 = a + ((c + d) + b) = a + (c + d) + b [comm of b and c+d]
    //                 = (a + c + d) + b ... hmm this is getting complex
    // Let's use add_rearrange_2x2: (a+b) + (c+d) ≡ (a+c) + (b+d)
    // where a = -(wz), b = -(xy), c = yx, d = zw
    // But first we need to show the expression as (-(wz) + -(xy)) + (yx + zw)

    // We have: -(wz) + -(xy) + yx + zw
    // Group as: (-(wz) + -(xy)) + (yx + zw)
    T::axiom_add_associative(w.mul(z).neg().add(x.mul(y).neg()), y.mul(x), z.mul(w));
    T::axiom_eqv_symmetric(
        w.mul(z).neg().add(x.mul(y).neg()).add(y.mul(x)).add(z.mul(w)),
        w.mul(z).neg().add(x.mul(y).neg()).add(y.mul(x).add(z.mul(w))),
    );

    // Swap yx+zw → zw+yx so rearrange_2x2 gives the right pairing
    T::axiom_add_commutative(y.mul(x), z.mul(w));
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        w.mul(z).neg().add(x.mul(y).neg()),
        y.mul(x).add(z.mul(w)),
        z.mul(w).add(y.mul(x)),
    );
    // (-(wz)+-(xy)) + (zw+yx) ≡ (-(wz)+zw) + (-(xy)+yx)
    additive_group_lemmas::lemma_add_rearrange_2x2::<T>(
        w.mul(z).neg(), x.mul(y).neg(), z.mul(w), y.mul(x),
    );
    // Chain: (-(wz)+-(xy))+(yx+zw) → swapped → rearranged
    T::axiom_eqv_transitive(
        w.mul(z).neg().add(x.mul(y).neg()).add(y.mul(x).add(z.mul(w))),
        w.mul(z).neg().add(x.mul(y).neg()).add(z.mul(w).add(y.mul(x))),
        w.mul(z).neg().add(z.mul(w)).add(x.mul(y).neg().add(y.mul(x))),
    );

    // -(wz) + zw ≡ -(wz) + wz ≡ 0
    T::axiom_mul_commutative(z, w);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        w.mul(z).neg(), z.mul(w), w.mul(z),
    );
    additive_group_lemmas::lemma_add_inverse_left::<T>(w.mul(z));
    T::axiom_eqv_transitive(
        w.mul(z).neg().add(z.mul(w)),
        w.mul(z).neg().add(w.mul(z)),
        T::zero(),
    );

    // -(xy) + yx ≡ 0
    T::axiom_mul_commutative(y, x);
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        x.mul(y).neg(), y.mul(x), x.mul(y),
    );
    additive_group_lemmas::lemma_add_inverse_left::<T>(x.mul(y));
    T::axiom_eqv_transitive(
        x.mul(y).neg().add(y.mul(x)),
        x.mul(y).neg().add(x.mul(y)),
        T::zero(),
    );

    // 0 + 0 ≡ 0
    additive_group_lemmas::lemma_add_congruence::<T>(
        w.mul(z).neg().add(z.mul(w)), T::zero(),
        x.mul(y).neg().add(y.mul(x)), T::zero(),
    );
    T::axiom_add_zero_right(T::zero());
    T::axiom_eqv_transitive(
        w.mul(z).neg().add(z.mul(w)).add(x.mul(y).neg().add(y.mul(x))),
        T::zero().add(T::zero()),
        T::zero(),
    );

    // Now connect back through all the chains
    // We need to connect from the original add_assoc'd form to the rearranged form
    T::axiom_eqv_transitive(
        w.mul(z).neg().add(x.mul(y).neg()).add(y.mul(x).add(z.mul(w))),
        w.mul(z).neg().add(x.mul(y).neg()).add(z.mul(w).add(y.mul(x))),
        w.mul(z).neg().add(z.mul(w)).add(x.mul(y).neg().add(y.mul(x))),
    );

    // Connect from flat form to assoc form
    T::axiom_eqv_transitive(
        w.mul(z).neg().add(x.mul(y).neg()).add(y.mul(x).add(z.mul(w))),
        w.mul(z).neg().add(z.mul(w)).add(x.mul(y).neg().add(y.mul(x))),
        T::zero(),
    );
    T::axiom_eqv_transitive(
        w.mul(z).neg().add(x.mul(y).neg()).add(y.mul(x)).add(z.mul(w)),
        w.mul(z).neg().add(x.mul(y).neg()).add(y.mul(x).add(z.mul(w))),
        T::zero(),
    );

    // Connect from the mul expression
    T::axiom_eqv_transitive(
        w.mul(z.neg()).add(x.mul(y.neg())).sub(y.mul(x.neg())).add(z.mul(w)),
        w.mul(z).neg().add(x.mul(y).neg()).add(y.mul(x)).add(z.mul(w)),
        T::zero(),
    );
}

/// mul(q, conjugate(q)) ≡ real(norm_sq(q))
pub proof fn lemma_mul_conjugate_right<T: Ring>(q: Quat<T>)
    ensures mul(q, conjugate(q)).eqv(real(norm_sq(q))),
{
    lemma_mul_conj_w(q);
    lemma_mul_conj_x(q);
    lemma_mul_conj_y(q);
    lemma_mul_conj_z(q);
    // real(norm_sq(q)) = Quat { w: norm_sq(q), x: 0, y: 0, z: 0 }
    // So we need x ≡ 0, y ≡ 0, z ≡ 0 which we proved above
}

/// mul(conjugate(q), q) ≡ real(norm_sq(q))
pub proof fn lemma_mul_conjugate_left<T: Ring>(q: Quat<T>)
    ensures mul(conjugate(q), q).eqv(real(norm_sq(q))),
{
    // conj(conj(q)) ≡ q
    lemma_conjugate_involution(q);
    // mul_conjugate_right(conj(q)): mul(conj(q), conj(conj(q))) ≡ real(norm_sq(conj(q)))
    lemma_mul_conjugate_right(conjugate(q));
    // mul(conj(q), conj(conj(q))) ≡ mul(conj(q), q)
    lemma_mul_congruence_right(conjugate(q), conjugate(conjugate(q)), q);
    Quat::<T>::axiom_eqv_symmetric(
        mul(conjugate(q), conjugate(conjugate(q))),
        mul(conjugate(q), q),
    );
    // So mul(conj(q), q) ≡ real(norm_sq(conj(q)))
    Quat::<T>::axiom_eqv_transitive(
        mul(conjugate(q), q),
        mul(conjugate(q), conjugate(conjugate(q))),
        real(norm_sq(conjugate(q))),
    );
    // norm_sq(conj(q)) ≡ norm_sq(q)
    lemma_norm_sq_conjugate_invariant(q);
    // real(norm_sq(conj(q))) ≡ real(norm_sq(q))
    lemma_real_congruence(norm_sq(conjugate(q)), norm_sq(q));
    Quat::<T>::axiom_eqv_transitive(
        mul(conjugate(q), q),
        real(norm_sq(conjugate(q))),
        real(norm_sq(q)),
    );
}

/// norm_sq(conjugate(q)) ≡ norm_sq(q)
pub proof fn lemma_norm_sq_conjugate_invariant<T: Ring>(q: Quat<T>)
    ensures norm_sq(conjugate(q)).eqv(norm_sq(q)),
{
    // conj(q) = (q.w, -q.x, -q.y, -q.z)
    // norm_sq(conj(q)) = q.w*q.w + (-q.x)*(-q.x) + (-q.y)*(-q.y) + (-q.z)*(-q.z)
    // (-a)*(-a) ≡ a*a by neg_mul_neg
    T::axiom_eqv_reflexive(q.w.mul(q.w));
    ring_lemmas::lemma_neg_mul_neg::<T>(q.x, q.x);
    ring_lemmas::lemma_neg_mul_neg::<T>(q.y, q.y);
    ring_lemmas::lemma_neg_mul_neg::<T>(q.z, q.z);
    additive_group_lemmas::lemma_add_congruence::<T>(
        q.w.mul(q.w), q.w.mul(q.w),
        q.x.neg().mul(q.x.neg()), q.x.mul(q.x),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        q.w.mul(q.w).add(q.x.neg().mul(q.x.neg())),
        q.w.mul(q.w).add(q.x.mul(q.x)),
        q.y.neg().mul(q.y.neg()), q.y.mul(q.y),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        q.w.mul(q.w).add(q.x.neg().mul(q.x.neg())).add(q.y.neg().mul(q.y.neg())),
        q.w.mul(q.w).add(q.x.mul(q.x)).add(q.y.mul(q.y)),
        q.z.neg().mul(q.z.neg()), q.z.mul(q.z),
    );
}

/// real preserves equivalence
pub proof fn lemma_real_congruence<T: Ring>(s: T, t: T)
    requires s.eqv(t),
    ensures real(s).eqv(real(t)),
{
    T::axiom_eqv_reflexive(T::zero());
}

// ===========================================================================
// norm_sq(scale(k, q)) ≡ k*k * norm_sq(q)
// ===========================================================================

/// norm_sq(scale(k, q)) ≡ k.mul(k).mul(norm_sq(q))
pub proof fn lemma_norm_sq_scale<T: Ring>(k: T, q: Quat<T>)
    ensures norm_sq(scale(k, q)).eqv(k.mul(k).mul(norm_sq(q))),
{
    // scale(k, q) = (k*w, k*x, k*y, k*z)
    // norm_sq = (k*w)*(k*w) + (k*x)*(k*x) + (k*y)*(k*y) + (k*z)*(k*z)
    // (k*a)*(k*a) = k*(a*(k*a)) = k*(a*k*a) = k*(k*a*a) [comm] = k*k*(a*a)
    // So norm_sq = k*k*(w*w + x*x + y*y + z*z) = k*k*norm_sq(q)

    // (k*a)*(k*a) ≡ k*(k*(a*a))
    // by assoc: (k*a)*(k*a) = k*(a*(k*a))
    // then a*(k*a) = (a*k)*a = (k*a)*a [comm] = k*(a*a)
    // so k*(a*(k*a)) = k*(k*(a*a))

    // For each component, show (k*c)*(k*c) ≡ k*k * (c*c)
    lemma_sq_scale_factor::<T>(k, q.w);
    lemma_sq_scale_factor::<T>(k, q.x);
    lemma_sq_scale_factor::<T>(k, q.y);
    lemma_sq_scale_factor::<T>(k, q.z);

    // Congruence on sum
    additive_group_lemmas::lemma_add_congruence::<T>(
        k.mul(q.w).mul(k.mul(q.w)), k.mul(k).mul(q.w.mul(q.w)),
        k.mul(q.x).mul(k.mul(q.x)), k.mul(k).mul(q.x.mul(q.x)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        k.mul(q.w).mul(k.mul(q.w)).add(k.mul(q.x).mul(k.mul(q.x))),
        k.mul(k).mul(q.w.mul(q.w)).add(k.mul(k).mul(q.x.mul(q.x))),
        k.mul(q.y).mul(k.mul(q.y)), k.mul(k).mul(q.y.mul(q.y)),
    );
    additive_group_lemmas::lemma_add_congruence::<T>(
        k.mul(q.w).mul(k.mul(q.w)).add(k.mul(q.x).mul(k.mul(q.x))).add(k.mul(q.y).mul(k.mul(q.y))),
        k.mul(k).mul(q.w.mul(q.w)).add(k.mul(k).mul(q.x.mul(q.x))).add(k.mul(k).mul(q.y.mul(q.y))),
        k.mul(q.z).mul(k.mul(q.z)), k.mul(k).mul(q.z.mul(q.z)),
    );

    // Factor: k²·(w²) + k²·(x²) + k²·(y²) + k²·(z²) ≡ k²·(w²+x²+y²+z²)
    // Use distribution: k²·a + k²·b = k²·(a+b)
    let kk = k.mul(k);
    T::axiom_mul_distributes_left(kk, q.w.mul(q.w), q.x.mul(q.x));
    T::axiom_eqv_symmetric(
        kk.mul(q.w.mul(q.w).add(q.x.mul(q.x))),
        kk.mul(q.w.mul(q.w)).add(kk.mul(q.x.mul(q.x))),
    );
    T::axiom_mul_distributes_left(kk, q.w.mul(q.w).add(q.x.mul(q.x)), q.y.mul(q.y));
    T::axiom_eqv_symmetric(
        kk.mul(q.w.mul(q.w).add(q.x.mul(q.x)).add(q.y.mul(q.y))),
        kk.mul(q.w.mul(q.w).add(q.x.mul(q.x))).add(kk.mul(q.y.mul(q.y))),
    );
    T::axiom_eqv_reflexive(kk.mul(q.y.mul(q.y)));
    additive_group_lemmas::lemma_add_congruence::<T>(
        kk.mul(q.w.mul(q.w)).add(kk.mul(q.x.mul(q.x))),
        kk.mul(q.w.mul(q.w).add(q.x.mul(q.x))),
        kk.mul(q.y.mul(q.y)), kk.mul(q.y.mul(q.y)),
    );
    T::axiom_eqv_transitive(
        kk.mul(q.w.mul(q.w)).add(kk.mul(q.x.mul(q.x))).add(kk.mul(q.y.mul(q.y))),
        kk.mul(q.w.mul(q.w).add(q.x.mul(q.x))).add(kk.mul(q.y.mul(q.y))),
        kk.mul(q.w.mul(q.w).add(q.x.mul(q.x)).add(q.y.mul(q.y))),
    );
    T::axiom_mul_distributes_left(kk, q.w.mul(q.w).add(q.x.mul(q.x)).add(q.y.mul(q.y)), q.z.mul(q.z));
    T::axiom_eqv_symmetric(
        kk.mul(q.w.mul(q.w).add(q.x.mul(q.x)).add(q.y.mul(q.y)).add(q.z.mul(q.z))),
        kk.mul(q.w.mul(q.w).add(q.x.mul(q.x)).add(q.y.mul(q.y))).add(kk.mul(q.z.mul(q.z))),
    );
    T::axiom_eqv_reflexive(kk.mul(q.z.mul(q.z)));
    additive_group_lemmas::lemma_add_congruence::<T>(
        kk.mul(q.w.mul(q.w)).add(kk.mul(q.x.mul(q.x))).add(kk.mul(q.y.mul(q.y))),
        kk.mul(q.w.mul(q.w).add(q.x.mul(q.x)).add(q.y.mul(q.y))),
        kk.mul(q.z.mul(q.z)), kk.mul(q.z.mul(q.z)),
    );
    T::axiom_eqv_transitive(
        kk.mul(q.w.mul(q.w)).add(kk.mul(q.x.mul(q.x))).add(kk.mul(q.y.mul(q.y))).add(kk.mul(q.z.mul(q.z))),
        kk.mul(q.w.mul(q.w).add(q.x.mul(q.x)).add(q.y.mul(q.y))).add(kk.mul(q.z.mul(q.z))),
        kk.mul(norm_sq(q)),
    );

    // Final chain
    T::axiom_eqv_transitive(
        norm_sq(scale(k, q)),
        kk.mul(q.w.mul(q.w)).add(kk.mul(q.x.mul(q.x))).add(kk.mul(q.y.mul(q.y))).add(kk.mul(q.z.mul(q.z))),
        kk.mul(norm_sq(q)),
    );
}

/// (k*c)*(k*c) ≡ (k*k)*(c*c)
pub proof fn lemma_sq_scale_factor<T: Ring>(k: T, c: T)
    ensures k.mul(c).mul(k.mul(c)).eqv(k.mul(k).mul(c.mul(c))),
{
    // (k*c)*(k*c) = k*(c*(k*c)) by assoc
    T::axiom_mul_associative(k, c, k.mul(c));
    T::axiom_eqv_symmetric(k.mul(c).mul(k.mul(c)), k.mul(c.mul(k.mul(c))));
    // c*(k*c) = (c*k)*c by assoc
    T::axiom_mul_associative(c, k, c);
    T::axiom_eqv_symmetric(c.mul(k).mul(c), c.mul(k.mul(c)));
    // c*k ≡ k*c by comm
    T::axiom_mul_commutative(c, k);
    // (c*k)*c ≡ (k*c)*c
    T::axiom_mul_congruence_left(c.mul(k), k.mul(c), c);
    // (k*c)*c = k*(c*c) by assoc
    T::axiom_mul_associative(k, c, c);
    T::axiom_eqv_symmetric(k.mul(c).mul(c), k.mul(c.mul(c)));
    // Chain: c*(k*c) ≡ (c*k)*c ≡ (k*c)*c ≡ k*(c*c)
    T::axiom_eqv_transitive(c.mul(k.mul(c)), c.mul(k).mul(c), k.mul(c).mul(c));
    T::axiom_eqv_transitive(c.mul(k.mul(c)), k.mul(c).mul(c), k.mul(c.mul(c)));
    // k*(c*(k*c)) ≡ k*(k*(c*c))
    ring_lemmas::lemma_mul_congruence_right::<T>(k, c.mul(k.mul(c)), k.mul(c.mul(c)));
    // k*(k*(c*c)) ≡ (k*k)*(c*c) by assoc (reversed)
    T::axiom_mul_associative(k, k, c.mul(c));
    T::axiom_eqv_symmetric(k.mul(k).mul(c.mul(c)), k.mul(k.mul(c.mul(c))));
    // Chain: (k*c)*(k*c) ≡ k*(c*(k*c)) ≡ k*(k*(c*c)) ≡ (k*k)*(c*c)
    T::axiom_eqv_transitive(
        k.mul(c).mul(k.mul(c)),
        k.mul(c.mul(k.mul(c))),
        k.mul(k.mul(c.mul(c))),
    );
    T::axiom_eqv_transitive(
        k.mul(c).mul(k.mul(c)),
        k.mul(k.mul(c.mul(c))),
        k.mul(k).mul(c.mul(c)),
    );
}

// ===========================================================================
// norm_sq(mul(a, b)) ≡ norm_sq(a) * norm_sq(b)  (Euler product identity)
// ===========================================================================

/// norm_sq(mul(a, b)) ≡ norm_sq(a).mul(norm_sq(b))
///
/// Proof chain:
/// 1. mul(ab, conj(ab)) ≡ real(norm_sq(ab))
/// 2. conj(ab) ≡ conj(b)·conj(a)
/// 3. mul(ab, conj(b)·conj(a)) ≡ mul(a, mul(b, conj(b))·conj(a))  [assoc]
///    ≡ mul(a, mul(real(norm_sq(b)), conj(a)))  [mul_conj_right]
///    ≡ mul(a, scale(norm_sq(b), conj(a)))      [mul_real_left]
///    ≡ scale(norm_sq(b), mul(a, conj(a)))      [mul_scale_right]
///    ≡ scale(norm_sq(b), real(norm_sq(a)))      [mul_conj_right]
///    ≡ real(norm_sq(b) * norm_sq(a))            [real_scale]
///    ≡ real(norm_sq(a) * norm_sq(b))            [commutativity]
/// 4. So real(norm_sq(ab)) ≡ real(norm_sq(a)*norm_sq(b))
///    → norm_sq(ab) ≡ norm_sq(a)*norm_sq(b) (w-components)
pub proof fn lemma_norm_sq_mul<T: Ring>(a: Quat<T>, b: Quat<T>)
    ensures norm_sq(mul(a, b)).eqv(norm_sq(a).mul(norm_sq(b))),
{
    let ab = mul(a, b);

    // Step 1: mul(ab, conj(ab)) ≡ real(norm_sq(ab))
    lemma_mul_conjugate_right(ab);

    // Step 2: conj(ab) ≡ conj(b)*conj(a)
    lemma_conjugate_mul_reverse(a, b);

    // Step 3: mul(ab, conj(ab)) ≡ mul(ab, conj(b)*conj(a))
    lemma_mul_congruence_right(ab, conjugate(ab), mul(conjugate(b), conjugate(a)));

    // mul(ab, conj(b)*conj(a)) ≡ mul(a, mul(b, conj(b)*conj(a)))  via assoc
    lemma_mul_associative(a, b, mul(conjugate(b), conjugate(a)));
    Quat::<T>::axiom_eqv_symmetric(
        mul(mul(a, b), mul(conjugate(b), conjugate(a))),
        mul(a, mul(b, mul(conjugate(b), conjugate(a)))),
    );

    // mul(b, mul(conj(b), conj(a))) ≡ mul(mul(b, conj(b)), conj(a))  via assoc (reversed)
    lemma_mul_associative(b, conjugate(b), conjugate(a));
    Quat::<T>::axiom_eqv_symmetric(
        mul(mul(b, conjugate(b)), conjugate(a)),
        mul(b, mul(conjugate(b), conjugate(a))),
    );

    // mul(b, conj(b)) ≡ real(norm_sq(b))
    lemma_mul_conjugate_right(b);

    // mul(mul(b, conj(b)), conj(a)) ≡ mul(real(norm_sq(b)), conj(a))
    lemma_mul_congruence_left(mul(b, conjugate(b)), real(norm_sq(b)), conjugate(a));

    // mul(real(norm_sq(b)), conj(a)) ≡ scale(norm_sq(b), conj(a))
    lemma_mul_real_left(norm_sq(b), conjugate(a));
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(b, conjugate(b)), conjugate(a)),
        mul(real(norm_sq(b)), conjugate(a)),
        scale(norm_sq(b), conjugate(a)),
    );

    // mul(b, mul(conj(b), conj(a))) ≡ scale(norm_sq(b), conj(a))
    Quat::<T>::axiom_eqv_transitive(
        mul(b, mul(conjugate(b), conjugate(a))),
        mul(mul(b, conjugate(b)), conjugate(a)),
        scale(norm_sq(b), conjugate(a)),
    );

    // mul(a, mul(b, mul(conj(b), conj(a)))) ≡ mul(a, scale(norm_sq(b), conj(a)))
    lemma_mul_congruence_right(a, mul(b, mul(conjugate(b), conjugate(a))), scale(norm_sq(b), conjugate(a)));

    // mul(a, scale(norm_sq(b), conj(a))) ≡ scale(norm_sq(b), mul(a, conj(a)))
    lemma_mul_scale_right(a, norm_sq(b), conjugate(a));
    Quat::<T>::axiom_eqv_transitive(
        mul(a, mul(b, mul(conjugate(b), conjugate(a)))),
        mul(a, scale(norm_sq(b), conjugate(a))),
        scale(norm_sq(b), mul(a, conjugate(a))),
    );

    // mul(a, conj(a)) ≡ real(norm_sq(a))
    lemma_mul_conjugate_right(a);
    lemma_scale_congruence(norm_sq(b), mul(a, conjugate(a)), real(norm_sq(a)));

    // scale(norm_sq(b), real(norm_sq(a))) ≡ real(norm_sq(b) * norm_sq(a))
    lemma_real_scale(norm_sq(b), norm_sq(a));

    // Chain: mul(a, mul(b, mul(conj(b), conj(a)))) ≡ real(norm_sq(b)*norm_sq(a))
    Quat::<T>::axiom_eqv_transitive(
        scale(norm_sq(b), mul(a, conjugate(a))),
        scale(norm_sq(b), real(norm_sq(a))),
        real(norm_sq(b).mul(norm_sq(a))),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(a, mul(b, mul(conjugate(b), conjugate(a)))),
        scale(norm_sq(b), mul(a, conjugate(a))),
        real(norm_sq(b).mul(norm_sq(a))),
    );

    // mul(ab, mul(conj(b), conj(a))) ≡ mul(a, mul(b, mul(conj(b), conj(a))))
    //                                ≡ real(norm_sq(b)*norm_sq(a))
    Quat::<T>::axiom_eqv_transitive(
        mul(ab, mul(conjugate(b), conjugate(a))),
        mul(a, mul(b, mul(conjugate(b), conjugate(a)))),
        real(norm_sq(b).mul(norm_sq(a))),
    );

    // mul(ab, conj(ab)) ≡ mul(ab, mul(conj(b), conj(a)))
    //                    ≡ real(norm_sq(b)*norm_sq(a))
    Quat::<T>::axiom_eqv_transitive(
        mul(ab, conjugate(ab)),
        mul(ab, mul(conjugate(b), conjugate(a))),
        real(norm_sq(b).mul(norm_sq(a))),
    );

    // mul(ab, conj(ab)) ≡ real(norm_sq(ab))  [from step 1]
    // So real(norm_sq(ab)) ≡ real(norm_sq(b)*norm_sq(a))
    Quat::<T>::axiom_eqv_symmetric(
        mul(ab, conjugate(ab)),
        real(norm_sq(ab)),
    );
    Quat::<T>::axiom_eqv_transitive(
        real(norm_sq(ab)),
        mul(ab, conjugate(ab)),
        real(norm_sq(b).mul(norm_sq(a))),
    );

    // Extract w-component: norm_sq(ab) ≡ norm_sq(b)*norm_sq(a)
    // (real(s).eqv(real(t)) gives s.eqv(t) via w-component)

    // Commutativity: norm_sq(b)*norm_sq(a) ≡ norm_sq(a)*norm_sq(b)
    T::axiom_mul_commutative(norm_sq(b), norm_sq(a));
    T::axiom_eqv_transitive(
        norm_sq(ab),
        norm_sq(b).mul(norm_sq(a)),
        norm_sq(a).mul(norm_sq(b)),
    );
}

} // verus!
