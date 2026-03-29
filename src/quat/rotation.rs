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
use super::norm::{
    lemma_norm_sq_congruence,
    lemma_norm_sq_mul,
    lemma_mul_conjugate_right,
    lemma_norm_sq_conjugate_invariant,
};
use super::inverse::lemma_norm_sq_one;
use crate::vec3::Vec3;

verus! {

//  ===========================================================================
//  Spec functions
//  ===========================================================================

///  Embed a 3D vector as a pure quaternion (0, x, y, z)
pub open spec fn pure_vec3<T: Ring>(v: Vec3<T>) -> Quat<T> {
    Quat { w: T::zero(), x: v.x, y: v.y, z: v.z }
}

///  Extract the vector part of a quaternion
pub open spec fn vector_part<T: Ring>(q: Quat<T>) -> Vec3<T> {
    Vec3 { x: q.x, y: q.y, z: q.z }
}

///  Rotation quaternion product: q * pure(v) * conj(q)
pub open spec fn rotate_quat<T: Ring>(v: Vec3<T>, q: Quat<T>) -> Quat<T> {
    mul(q, mul(pure_vec3(v), conjugate(q)))
}

///  Rotate a vector by quaternion q: vector_part(q * pure(v) * conj(q))
pub open spec fn rotate_vec3<T: Ring>(v: Vec3<T>, q: Quat<T>) -> Vec3<T> {
    vector_part(rotate_quat(v, q))
}

///  Unit quaternion predicate: norm_sq(q) ≡ one
pub open spec fn is_unit<T: Ring>(q: Quat<T>) -> bool {
    norm_sq(q).eqv(T::one())
}

//  ===========================================================================
//  Congruence lemmas
//  ===========================================================================

///  pure_vec3 preserves equivalence
pub proof fn lemma_pure_vec3_congruence<T: Ring>(u: Vec3<T>, v: Vec3<T>)
    requires u.eqv(v),
    ensures pure_vec3(u).eqv(pure_vec3(v)),
{
    T::axiom_eqv_reflexive(T::zero());
}

///  vector_part preserves equivalence
pub proof fn lemma_vector_part_congruence<T: Ring>(a: Quat<T>, b: Quat<T>)
    requires a.eqv(b),
    ensures vector_part(a).eqv(vector_part(b)),
{
    //  a.eqv(b) gives a.x ≡ b.x, a.y ≡ b.y, a.z ≡ b.z
}

//  ===========================================================================
//  Pure quaternion properties
//  ===========================================================================

///  conj(pure(v)) ≡ neg(pure(v))
///  Because conj(0, x, y, z) = (0, -x, -y, -z) = -(0, x, y, z)
pub proof fn lemma_pure_vec3_conjugate_neg<T: Ring>(v: Vec3<T>)
    ensures conjugate(pure_vec3(v)).eqv(pure_vec3(v).neg()),
{
    //  conj(pure(v)) = (0, -x, -y, -z)
    //  neg(pure(v)) = (-0, -x, -y, -z)
    //  Need: 0 ≡ -0
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_symmetric(T::zero().neg(), T::zero());
    //  x, y, z match trivially via reflexive
    T::axiom_eqv_reflexive(v.x.neg());
    T::axiom_eqv_reflexive(v.y.neg());
    T::axiom_eqv_reflexive(v.z.neg());
}

///  pure_vec3(v) has w ≡ 0
pub proof fn lemma_pure_vec3_w_zero<T: Ring>(v: Vec3<T>)
    ensures pure_vec3(v).w.eqv(T::zero()),
{
    T::axiom_eqv_reflexive(T::zero());
}

//  ===========================================================================
//  Rotation norm preservation
//  ===========================================================================

///  For unit quaternion q: norm_sq(rotate_quat(v, q)) ≡ norm_sq(pure_vec3(v))
///
///  Proof:
///  rotate_quat(v, q) = q * pure(v) * conj(q)
///  norm_sq(q * pure(v) * conj(q))
///  ≡ norm_sq(q) * norm_sq(pure(v) * conj(q))     [norm_sq_mul]
///  ≡ norm_sq(q) * (norm_sq(pure(v)) * norm_sq(conj(q)))  [norm_sq_mul]
///  ≡ 1 * (norm_sq(pure(v)) * norm_sq(q))           [unit + conj_invariant]
///  ≡ 1 * (norm_sq(pure(v)) * 1)                    [unit]
///  ≡ 1 * norm_sq(pure(v))                          [mul_one_right]
///  ≡ norm_sq(pure(v))                               [mul_one_left]
pub proof fn lemma_rotate_quat_norm_sq<T: Ring>(v: Vec3<T>, q: Quat<T>)
    requires is_unit(q),
    ensures norm_sq(rotate_quat(v, q)).eqv(norm_sq(pure_vec3(v))),
{
    let p = pure_vec3(v);
    let cq = conjugate(q);

    //  norm_sq(q * (p * cq)) ≡ norm_sq(q) * norm_sq(p * cq)
    lemma_norm_sq_mul(q, mul(p, cq));

    //  norm_sq(p * cq) ≡ norm_sq(p) * norm_sq(cq)
    lemma_norm_sq_mul(p, cq);

    //  norm_sq(cq) ≡ norm_sq(q) ≡ 1
    lemma_norm_sq_conjugate_invariant(q);
    T::axiom_eqv_transitive(norm_sq(cq), norm_sq(q), T::one());

    //  norm_sq(p) * norm_sq(cq) ≡ norm_sq(p) * 1
    ring_lemmas::lemma_mul_congruence_right::<T>(norm_sq(p), norm_sq(cq), T::one());

    //  norm_sq(p) * 1 ≡ norm_sq(p)
    T::axiom_mul_one_right(norm_sq(p));

    //  Chain: norm_sq(p * cq) ≡ norm_sq(p) * norm_sq(cq) ≡ norm_sq(p) * 1 ≡ norm_sq(p)
    T::axiom_eqv_transitive(
        norm_sq(p).mul(norm_sq(cq)),
        norm_sq(p).mul(T::one()),
        norm_sq(p),
    );
    T::axiom_eqv_transitive(
        norm_sq(mul(p, cq)),
        norm_sq(p).mul(norm_sq(cq)),
        norm_sq(p),
    );

    //  norm_sq(q) * norm_sq(p * cq) ≡ 1 * norm_sq(p * cq) ≡ norm_sq(p * cq) ≡ norm_sq(p)
    ring_lemmas::lemma_mul_congruence::<T>(
        norm_sq(q), T::one(),
        norm_sq(mul(p, cq)), norm_sq(p),
    );
    //  1 * norm_sq(p) ≡ norm_sq(p)
    T::axiom_mul_commutative(T::one(), norm_sq(p));
    T::axiom_mul_one_right(norm_sq(p));
    T::axiom_eqv_transitive(
        T::one().mul(norm_sq(p)),
        norm_sq(p).mul(T::one()),
        norm_sq(p),
    );
    //  norm_sq(q) * norm_sq(p*cq) ≡ 1 * norm_sq(p) ≡ norm_sq(p)
    T::axiom_eqv_transitive(
        norm_sq(q).mul(norm_sq(mul(p, cq))),
        T::one().mul(norm_sq(p)),
        norm_sq(p),
    );
    //  norm_sq(rotate_quat) ≡ norm_sq(q) * norm_sq(p*cq) ≡ norm_sq(p)
    T::axiom_eqv_transitive(
        norm_sq(rotate_quat(v, q)),
        norm_sq(q).mul(norm_sq(mul(p, cq))),
        norm_sq(p),
    );
}

//  ===========================================================================
//  Rotation composition
//  ===========================================================================

///  rotate_quat(v, q1*q2) ≡ rotate_quat(rotate_vec3(v, q2), q1)
///  ... when both q1, q2 are unit quaternions.
///
///  This requires:
///  (q1*q2) * pure(v) * conj(q1*q2)
///  ≡ (q1*q2) * pure(v) * (conj(q2)*conj(q1))   [conj_mul_reverse]
///  ≡ q1 * (q2 * pure(v) * conj(q2)) * conj(q1)  [assoc]
///
///  Proof deferred — requires showing w-component of
///  q2*pure(v)*conj(q2) is zero, enabling vector_part extraction.

//  ===========================================================================
//  Rotate congruence
//  ===========================================================================

///  rotate_quat preserves equivalence of vectors
pub proof fn lemma_rotate_quat_congruence_vec<T: Ring>(
    u: Vec3<T>, v: Vec3<T>, q: Quat<T>,
)
    requires u.eqv(v),
    ensures rotate_quat(u, q).eqv(rotate_quat(v, q)),
{
    lemma_pure_vec3_congruence(u, v);
    lemma_mul_congruence_left(pure_vec3(u), pure_vec3(v), conjugate(q));
    lemma_mul_congruence_right(q, mul(pure_vec3(u), conjugate(q)), mul(pure_vec3(v), conjugate(q)));
}

///  rotate_quat preserves equivalence of quaternions
pub proof fn lemma_rotate_quat_congruence_q<T: Ring>(
    v: Vec3<T>, q1: Quat<T>, q2: Quat<T>,
)
    requires q1.eqv(q2),
    ensures rotate_quat(v, q1).eqv(rotate_quat(v, q2)),
{
    let p = pure_vec3(v);
    lemma_conjugate_congruence(q1, q2);
    lemma_mul_congruence_right(p, conjugate(q1), conjugate(q2));
    lemma_mul_congruence_right(q1, mul(p, conjugate(q1)), mul(p, conjugate(q2)));
    lemma_mul_congruence_left(q1, q2, mul(p, conjugate(q2)));
    Quat::<T>::axiom_eqv_transitive(
        mul(q1, mul(p, conjugate(q1))),
        mul(q1, mul(p, conjugate(q2))),
        mul(q2, mul(p, conjugate(q2))),
    );
}

///  rotate_vec3 preserves equivalence of vectors
pub proof fn lemma_rotate_vec3_congruence_vec<T: Ring>(
    u: Vec3<T>, v: Vec3<T>, q: Quat<T>,
)
    requires u.eqv(v),
    ensures rotate_vec3(u, q).eqv(rotate_vec3(v, q)),
{
    lemma_rotate_quat_congruence_vec(u, v, q);
    lemma_vector_part_congruence(rotate_quat(u, q), rotate_quat(v, q));
}

} //  verus!
