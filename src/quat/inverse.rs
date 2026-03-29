use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::field_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use super::Quat;
#[allow(unused_imports)]
use super::ops::*;
#[allow(unused_imports)]
use super::ops::mul;
use super::conjugate::*;
use super::norm::{
    lemma_norm_sq_congruence,
    lemma_mul_conjugate_right,
    lemma_mul_conjugate_left,
    lemma_real_scale,
    lemma_real_congruence,
};
#[allow(unused_imports)]
use super::norm::real as qreal;

verus! {

//  ===========================================================================
//  Quaternion inverse: q^(-1) = scale(recip(norm_sq(q)), conjugate(q))
//  ===========================================================================

///  Quaternion inverse: conj(q) / norm_sq(q)
pub open spec fn inverse<T: Field>(q: Quat<T>) -> Quat<T> {
    scale(norm_sq(q).recip(), conjugate(q))
}

///  inverse preserves equivalence
pub proof fn lemma_inverse_congruence<T: Field>(a: Quat<T>, b: Quat<T>)
    requires
        a.eqv(b),
        !norm_sq(a).eqv(T::zero()),
    ensures inverse(a).eqv(inverse(b)),
{
    lemma_conjugate_congruence(a, b);
    lemma_norm_sq_congruence(a, b);
    T::axiom_recip_congruence(norm_sq(a), norm_sq(b));
    lemma_scale_congruence_scalar(norm_sq(a).recip(), norm_sq(b).recip(), conjugate(a));
    lemma_scale_congruence(norm_sq(b).recip(), conjugate(a), conjugate(b));
    Quat::<T>::axiom_eqv_transitive(
        scale(norm_sq(a).recip(), conjugate(a)),
        scale(norm_sq(b).recip(), conjugate(a)),
        scale(norm_sq(b).recip(), conjugate(b)),
    );
}

///  q * q^(-1) ≡ one()
///
///  Proof:
///  q * scale(recip(n), conj(q))
///  ≡ scale(recip(n), q * conj(q))           [mul_scale_right]
///  ≡ scale(recip(n), real(n))               [mul_conjugate_right]
///  ≡ real(recip(n) * n)                     [real_scale]
///  = real(one()) = one()                    [mul_recip_left]
pub proof fn lemma_inverse_right<T: Field>(q: Quat<T>)
    requires !norm_sq(q).eqv(T::zero()),
    ensures mul(q, inverse(q)).eqv(one()),
{
    let n = norm_sq(q);

    //  q * scale(recip(n), conj(q)) ≡ scale(recip(n), q * conj(q))
    lemma_mul_scale_right(q, n.recip(), conjugate(q));

    //  q * conj(q) ≡ real(n)
    lemma_mul_conjugate_right(q);
    lemma_scale_congruence(n.recip(), mul(q, conjugate(q)), qreal(n));

    //  Chain: mul(q, inv(q)) ≡ scale(recip(n), q*conj(q)) ≡ scale(recip(n), real(n))
    Quat::<T>::axiom_eqv_transitive(
        mul(q, inverse(q)),
        scale(n.recip(), mul(q, conjugate(q))),
        scale(n.recip(), qreal(n)),
    );

    //  scale(recip(n), real(n)) ≡ real(recip(n) * n)
    lemma_real_scale(n.recip(), n);

    //  recip(n) * n ≡ one
    field_lemmas::lemma_mul_recip_left::<T>(n);

    //  real(recip(n) * n) ≡ real(one()) = one()
    lemma_real_congruence(n.recip().mul(n), T::one());

    //  Chain through to one()
    Quat::<T>::axiom_eqv_transitive(
        scale(n.recip(), qreal(n)),
        qreal(n.recip().mul(n)),
        one(),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(q, inverse(q)),
        scale(n.recip(), qreal(n)),
        one(),
    );
}

///  q^(-1) * q ≡ one()
///
///  Proof: same structure using mul_scale_left and mul_conjugate_left
pub proof fn lemma_inverse_left<T: Field>(q: Quat<T>)
    requires !norm_sq(q).eqv(T::zero()),
    ensures mul(inverse(q), q).eqv(one()),
{
    let n = norm_sq(q);

    //  scale(recip(n), conj(q)) * q ≡ scale(recip(n), conj(q) * q)
    lemma_mul_scale_left(n.recip(), conjugate(q), q);

    //  conj(q) * q ≡ real(n)
    lemma_mul_conjugate_left(q);
    lemma_scale_congruence(n.recip(), mul(conjugate(q), q), qreal(n));

    //  Chain
    Quat::<T>::axiom_eqv_transitive(
        mul(inverse(q), q),
        scale(n.recip(), mul(conjugate(q), q)),
        scale(n.recip(), qreal(n)),
    );

    //  scale(recip(n), real(n)) ≡ real(recip(n) * n) ≡ one()
    lemma_real_scale(n.recip(), n);
    field_lemmas::lemma_mul_recip_left::<T>(n);
    lemma_real_congruence(n.recip().mul(n), T::one());
    Quat::<T>::axiom_eqv_transitive(
        scale(n.recip(), qreal(n)),
        qreal(n.recip().mul(n)),
        one(),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(inverse(q), q),
        scale(n.recip(), qreal(n)),
        one(),
    );
}

///  norm_sq(one()) ≡ T::one()
pub proof fn lemma_norm_sq_one<T: Ring>()
    ensures norm_sq(one::<T>()).eqv(T::one()),
{
    //  norm_sq(one) = 1*1 + 0*0 + 0*0 + 0*0
    let o = T::one();
    let z = T::zero();
    T::axiom_mul_one_right(o);   //  1*1 ≡ 1
    T::axiom_mul_zero_right(z);  //  0*0 ≡ 0

    //  1*1 + 0*0 ≡ 1 + 0*0
    T::axiom_eqv_reflexive(z.mul(z));
    additive_group_lemmas::lemma_add_congruence::<T>(
        o.mul(o), o,
        z.mul(z), z.mul(z),
    );
    //  1 + 0*0 ≡ 1 + 0 ≡ 1
    additive_group_lemmas::lemma_add_congruence_right::<T>(
        o, z.mul(z), z,
    );
    T::axiom_add_zero_right(o);
    T::axiom_eqv_transitive(o.add(z.mul(z)), o.add(z), o);
    //  1*1 + 0*0 ≡ 1
    T::axiom_eqv_transitive(
        o.mul(o).add(z.mul(z)),
        o.add(z.mul(z)),
        o,
    );

    //  (1*1 + 0*0) + 0*0 ≡ 1 + 0*0 ≡ 1
    additive_group_lemmas::lemma_add_congruence::<T>(
        o.mul(o).add(z.mul(z)), o,
        z.mul(z), z.mul(z),
    );
    T::axiom_eqv_transitive(
        o.mul(o).add(z.mul(z)).add(z.mul(z)),
        o.add(z.mul(z)),
        o,
    );

    //  ((1*1 + 0*0) + 0*0) + 0*0 ≡ 1 + 0*0 ≡ 1
    additive_group_lemmas::lemma_add_congruence::<T>(
        o.mul(o).add(z.mul(z)).add(z.mul(z)), o,
        z.mul(z), z.mul(z),
    );
    T::axiom_eqv_transitive(
        norm_sq(one::<T>()),
        o.add(z.mul(z)),
        o,
    );
}

} //  verus!
