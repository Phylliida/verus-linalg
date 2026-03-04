use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use super::Quat;
#[allow(unused_imports)]
use super::ops::*;
#[allow(unused_imports)]
use super::ops::mul;
use super::basis::*;
use super::assoc::{basis_decompose, lemma_basis_decompose_eqv};

verus! {

// ===========================================================================
// Basic conjugate lemmas
// ===========================================================================

/// conj preserves equivalence
pub proof fn lemma_conjugate_congruence<T: Ring>(a: Quat<T>, b: Quat<T>)
    requires a.eqv(b),
    ensures conjugate(a).eqv(conjugate(b)),
{
    additive_group_lemmas::lemma_neg_congruence::<T>(a.x, b.x);
    additive_group_lemmas::lemma_neg_congruence::<T>(a.y, b.y);
    additive_group_lemmas::lemma_neg_congruence::<T>(a.z, b.z);
}

/// conj distributes over addition: conj(a+b) ≡ conj(a)+conj(b)
pub proof fn lemma_conjugate_add<T: Ring>(a: Quat<T>, b: Quat<T>)
    ensures conjugate(a.add(b)).eqv(conjugate(a).add(conjugate(b))),
{
    T::axiom_eqv_reflexive(a.w.add(b.w));
    additive_group_lemmas::lemma_neg_add::<T>(a.x, b.x);
    additive_group_lemmas::lemma_neg_add::<T>(a.y, b.y);
    additive_group_lemmas::lemma_neg_add::<T>(a.z, b.z);
}

/// conj commutes with scale: conj(scale(k,q)) ≡ scale(k, conj(q))
pub proof fn lemma_conjugate_scale<T: Ring>(k: T, q: Quat<T>)
    ensures conjugate(scale(k, q)).eqv(scale(k, conjugate(q))),
{
    T::axiom_eqv_reflexive(k.mul(q.w));
    // LHS comp = (k*q.x).neg(), RHS comp = k*(q.x.neg())
    // mul_neg_right: k*(q.x.neg()) ≡ (k*q.x).neg(); need symmetric
    ring_lemmas::lemma_mul_neg_right::<T>(k, q.x);
    T::axiom_eqv_symmetric(k.mul(q.x.neg()), k.mul(q.x).neg());
    ring_lemmas::lemma_mul_neg_right::<T>(k, q.y);
    T::axiom_eqv_symmetric(k.mul(q.y.neg()), k.mul(q.y).neg());
    ring_lemmas::lemma_mul_neg_right::<T>(k, q.z);
    T::axiom_eqv_symmetric(k.mul(q.z.neg()), k.mul(q.z).neg());
}

/// conj is involutory: conj(conj(q)) ≡ q
pub proof fn lemma_conjugate_involution<T: Ring>(q: Quat<T>)
    ensures conjugate(conjugate(q)).eqv(q),
{
    T::axiom_eqv_reflexive(q.w);
    additive_group_lemmas::lemma_neg_involution::<T>(q.x);
    additive_group_lemmas::lemma_neg_involution::<T>(q.y);
    additive_group_lemmas::lemma_neg_involution::<T>(q.z);
}

/// conj(one()) ≡ one()
proof fn lemma_conjugate_one<T: Ring>()
    ensures conjugate::<T>(one()).eqv(one()),
{
    T::axiom_eqv_reflexive(T::one());
    additive_group_lemmas::lemma_neg_zero::<T>();
}

/// For imaginary basis (i≥1): conj(basis(i)) ≡ basis(i).neg()
proof fn lemma_conjugate_imag_basis<T: Ring>(i: int)
    requires 1 <= i < 4,
    ensures conjugate::<T>(basis(i)).eqv(basis::<T>(i).neg()),
{
    // w: 0 ≡ 0.neg()
    additive_group_lemmas::lemma_neg_zero::<T>();
    T::axiom_eqv_symmetric(T::zero().neg(), T::zero());
    // remaining components: x.neg() ≡ x.neg() by reflexive
    T::axiom_eqv_reflexive(T::one().neg());
    T::axiom_eqv_reflexive(T::zero().neg());
}

// ===========================================================================
// Quaternion neg-mul helpers (via scale(-1, ...))
// ===========================================================================

/// q.neg() ≡ scale(-1, q)
proof fn lemma_neg_eq_scale_neg_one<T: Ring>(q: Quat<T>)
    ensures q.neg().eqv(scale(T::one().neg(), q)),
{
    // scale(1, q) ≡ q
    lemma_scale_identity(q);
    // scale(1, q).neg() ≡ q.neg()
    additive_group_lemmas::lemma_neg_congruence::<Quat<T>>(scale(T::one(), q), q);
    // scale(-1, q) ≡ scale(1, q).neg()
    lemma_scale_neg_scalar(T::one(), q);
    // Chain: scale(-1, q) ≡ scale(1,q).neg() ≡ q.neg()
    Quat::<T>::axiom_eqv_transitive(
        scale(T::one().neg(), q),
        scale(T::one(), q).neg(),
        q.neg(),
    );
    Quat::<T>::axiom_eqv_symmetric(scale(T::one().neg(), q), q.neg());
}

/// mul(a.neg(), b) ≡ mul(a, b).neg()
pub proof fn lemma_qmul_neg_left<T: Ring>(a: Quat<T>, b: Quat<T>)
    ensures mul(a.neg(), b).eqv(mul(a, b).neg()),
{
    lemma_neg_eq_scale_neg_one(a);
    lemma_mul_congruence_left(a.neg(), scale(T::one().neg(), a), b);
    lemma_mul_scale_left(T::one().neg(), a, b);
    Quat::<T>::axiom_eqv_transitive(
        mul(a.neg(), b),
        mul(scale(T::one().neg(), a), b),
        scale(T::one().neg(), mul(a, b)),
    );
    lemma_neg_eq_scale_neg_one(mul(a, b));
    Quat::<T>::axiom_eqv_symmetric(mul(a, b).neg(), scale(T::one().neg(), mul(a, b)));
    Quat::<T>::axiom_eqv_transitive(
        mul(a.neg(), b),
        scale(T::one().neg(), mul(a, b)),
        mul(a, b).neg(),
    );
}

/// mul(a, b.neg()) ≡ mul(a, b).neg()
pub proof fn lemma_qmul_neg_right<T: Ring>(a: Quat<T>, b: Quat<T>)
    ensures mul(a, b.neg()).eqv(mul(a, b).neg()),
{
    lemma_neg_eq_scale_neg_one(b);
    lemma_mul_congruence_right(a, b.neg(), scale(T::one().neg(), b));
    lemma_mul_scale_right(a, T::one().neg(), b);
    Quat::<T>::axiom_eqv_transitive(
        mul(a, b.neg()),
        mul(a, scale(T::one().neg(), b)),
        scale(T::one().neg(), mul(a, b)),
    );
    lemma_neg_eq_scale_neg_one(mul(a, b));
    Quat::<T>::axiom_eqv_symmetric(mul(a, b).neg(), scale(T::one().neg(), mul(a, b)));
    Quat::<T>::axiom_eqv_transitive(
        mul(a, b.neg()),
        scale(T::one().neg(), mul(a, b)),
        mul(a, b).neg(),
    );
}

/// mul(a.neg(), b.neg()) ≡ mul(a, b)
pub proof fn lemma_qneg_mul_neg<T: Ring>(a: Quat<T>, b: Quat<T>)
    ensures mul(a.neg(), b.neg()).eqv(mul(a, b)),
{
    lemma_qmul_neg_left(a, b.neg());
    lemma_qmul_neg_right(a, b);
    additive_group_lemmas::lemma_neg_congruence::<Quat<T>>(mul(a, b.neg()), mul(a, b).neg());
    additive_group_lemmas::lemma_neg_involution::<Quat<T>>(mul(a, b));
    Quat::<T>::axiom_eqv_transitive(
        mul(a.neg(), b.neg()),
        mul(a, b.neg()).neg(),
        mul(a, b).neg().neg(),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(a.neg(), b.neg()),
        mul(a, b).neg().neg(),
        mul(a, b),
    );
}

// ===========================================================================
// Scale-neg interaction
// ===========================================================================

/// scale(s, q.neg()) ≡ scale(s.neg(), q)
proof fn lemma_scale_neg_swap<T: Ring>(s: T, q: Quat<T>)
    ensures scale(s, q.neg()).eqv(scale(s.neg(), q)),
{
    lemma_scale_neg_vec(s, q);
    lemma_scale_neg_scalar(s, q);
    Quat::<T>::axiom_eqv_symmetric(scale(s.neg(), q), scale(s, q).neg());
    Quat::<T>::axiom_eqv_transitive(
        scale(s, q.neg()),
        scale(s, q).neg(),
        scale(s.neg(), q),
    );
}

/// sign_value(-s) ≡ sign_value(s).neg()
proof fn lemma_sign_value_neg<T: Ring>(s: int)
    requires s == 1 || s == -1,
    ensures sign_value::<T>(-s).eqv(sign_value::<T>(s).neg()),
{
    if s == 1 {
        T::axiom_eqv_reflexive(T::one().neg());
    } else {
        additive_group_lemmas::lemma_neg_involution::<T>(T::one());
        T::axiom_eqv_symmetric(T::one().neg().neg(), T::one());
    }
}

// ===========================================================================
// Conjugate-mul-reverse: bilinear lifting
// ===========================================================================

/// Instance predicate: conj(a*b) ≡ conj(b)*conj(a)
pub open spec fn conj_mul_rev<T: Ring>(a: Quat<T>, b: Quat<T>) -> bool {
    conjugate(mul(a, b)).eqv(mul(conjugate(b), conjugate(a)))
}

/// Basis case: conj(basis(i)*basis(j)) ≡ conj(basis(j))*conj(basis(i))
proof fn lemma_conj_mul_rev_basis<T: Ring>(i: int, j: int)
    requires 0 <= i < 4, 0 <= j < 4,
    ensures conj_mul_rev::<T>(basis(i), basis(j)),
{
    if i == 0 {
        // LHS: conj(mul(one(), bj)) ≡ conj(bj) via mul_one_left
        lemma_mul_one_left::<T>(basis(j));
        lemma_conjugate_congruence(mul(one::<T>(), basis(j)), basis(j));
        // RHS: mul(conj(bj), conj(one())) ≡ mul(conj(bj), one()) ≡ conj(bj)
        lemma_conjugate_one::<T>();
        lemma_mul_congruence_right(conjugate(basis::<T>(j)), conjugate(one::<T>()), one());
        lemma_mul_one_right(conjugate(basis::<T>(j)));
        Quat::<T>::axiom_eqv_transitive(
            mul(conjugate(basis(j)), conjugate(one())),
            mul(conjugate(basis(j)), one()),
            conjugate(basis(j)),
        );
        // Connect: LHS ≡ conj(bj) ≡ RHS
        Quat::<T>::axiom_eqv_symmetric(
            mul(conjugate(basis(j)), conjugate(one())),
            conjugate(basis(j)),
        );
        Quat::<T>::axiom_eqv_transitive(
            conjugate(mul(one(), basis(j))),
            conjugate(basis(j)),
            mul(conjugate(basis(j)), conjugate(one())),
        );
    } else if j == 0 {
        // LHS: conj(mul(bi, one())) ≡ conj(bi)
        lemma_mul_one_right::<T>(basis(i));
        lemma_conjugate_congruence(mul(basis::<T>(i), one()), basis(i));
        // RHS: mul(conj(one()), conj(bi)) ≡ mul(one(), conj(bi)) ≡ conj(bi)
        lemma_conjugate_one::<T>();
        lemma_mul_congruence_left(conjugate(one::<T>()), one(), conjugate(basis::<T>(i)));
        lemma_mul_one_left(conjugate(basis::<T>(i)));
        Quat::<T>::axiom_eqv_transitive(
            mul(conjugate(one()), conjugate(basis(i))),
            mul(one(), conjugate(basis(i))),
            conjugate(basis(i)),
        );
        Quat::<T>::axiom_eqv_symmetric(
            mul(conjugate(one::<T>()), conjugate(basis(i))),
            conjugate(basis(i)),
        );
        Quat::<T>::axiom_eqv_transitive(
            conjugate(mul(basis(i), one())),
            conjugate(basis(i)),
            mul(conjugate(one()), conjugate(basis(i))),
        );
    } else {
        // i, j >= 1
        let bi = basis::<T>(i);
        let bj = basis::<T>(j);
        let s_ij = basis_mul_sign(i, j);
        let k_ij = basis_mul_idx(i, j);
        let s_ji = basis_mul_sign(j, i);
        let k_ji = basis_mul_idx(j, i);

        // === RHS chain ===
        // conj(bj) ≡ bj.neg(), conj(bi) ≡ bi.neg()
        lemma_conjugate_imag_basis::<T>(i);
        lemma_conjugate_imag_basis::<T>(j);
        // mul(conj(bj), conj(bi)) ≡ mul(bj.neg(), bi.neg())
        lemma_mul_congruence_left(conjugate(bj), bj.neg(), conjugate(bi));
        lemma_mul_congruence_right(bj.neg(), conjugate(bi), bi.neg());
        Quat::<T>::axiom_eqv_transitive(
            mul(conjugate(bj), conjugate(bi)),
            mul(bj.neg(), conjugate(bi)),
            mul(bj.neg(), bi.neg()),
        );
        // ≡ mul(bj, bi)
        lemma_qneg_mul_neg(bj, bi);
        Quat::<T>::axiom_eqv_transitive(
            mul(conjugate(bj), conjugate(bi)),
            mul(bj.neg(), bi.neg()),
            mul(bj, bi),
        );
        // ≡ signed_basis(s_ji, k_ji)
        lemma_basis_mul_to_signed::<T>(j, i);
        Quat::<T>::axiom_eqv_transitive(
            mul(conjugate(bj), conjugate(bi)),
            mul(bj, bi),
            scale(sign_value(s_ji), basis(k_ji)),
        );

        // === LHS chain ===
        // mul(bi, bj) ≡ signed_basis(s_ij, k_ij)
        lemma_basis_mul_to_signed::<T>(i, j);
        lemma_conjugate_congruence(
            mul(bi, bj),
            scale(sign_value(s_ij), basis(k_ij)),
        );
        // conj(scale(sv, basis(k))) ≡ scale(sv, conj(basis(k)))
        lemma_conjugate_scale(sign_value::<T>(s_ij), basis(k_ij));
        Quat::<T>::axiom_eqv_transitive(
            conjugate(mul(bi, bj)),
            conjugate(scale(sign_value(s_ij), basis(k_ij))),
            scale(sign_value(s_ij), conjugate(basis(k_ij))),
        );

        if i == j {
            // k_ij = 0: conj(basis(0)) = conj(one()) ≡ one()
            lemma_conjugate_one::<T>();
            lemma_scale_congruence(sign_value::<T>(s_ij), conjugate(basis::<T>(k_ij)), one());
            Quat::<T>::axiom_eqv_transitive(
                conjugate(mul(bi, bj)),
                scale(sign_value(s_ij), conjugate(basis(k_ij))),
                scale(sign_value(s_ij), one()),
            );
            // LHS ≡ scale(sv(s_ij), one())
            // RHS ≡ scale(sv(s_ji), basis(k_ji))
            // When i==j: s_ji=s_ij, k_ji=0, basis(0)=one() → same expression
            Quat::<T>::axiom_eqv_symmetric(
                mul(conjugate(bj), conjugate(bi)),
                scale(sign_value(s_ji), basis(k_ji)),
            );
            Quat::<T>::axiom_eqv_transitive(
                conjugate(mul(bi, bj)),
                scale(sign_value(s_ij), one::<T>()),
                mul(conjugate(bj), conjugate(bi)),
            );
        } else {
            // k_ij >= 1: conj(basis(k)) ≡ basis(k).neg()
            lemma_conjugate_imag_basis::<T>(k_ij);
            lemma_scale_congruence(sign_value::<T>(s_ij), conjugate(basis::<T>(k_ij)), basis::<T>(k_ij).neg());
            Quat::<T>::axiom_eqv_transitive(
                conjugate(mul(bi, bj)),
                scale(sign_value(s_ij), conjugate(basis(k_ij))),
                scale(sign_value(s_ij), basis::<T>(k_ij).neg()),
            );
            // scale(sv, basis(k).neg()) ≡ scale(sv.neg(), basis(k))
            lemma_scale_neg_swap(sign_value::<T>(s_ij), basis(k_ij));
            Quat::<T>::axiom_eqv_transitive(
                conjugate(mul(bi, bj)),
                scale(sign_value(s_ij), basis::<T>(k_ij).neg()),
                scale(sign_value::<T>(s_ij).neg(), basis(k_ij)),
            );
            // sv(s_ij).neg() ≡ sv(-s_ij)
            lemma_sign_value_neg::<T>(s_ij);
            T::axiom_eqv_symmetric(sign_value::<T>(-s_ij), sign_value::<T>(s_ij).neg());
            lemma_scale_congruence_scalar(sign_value::<T>(s_ij).neg(), sign_value::<T>(-s_ij), basis(k_ij));
            Quat::<T>::axiom_eqv_transitive(
                conjugate(mul(bi, bj)),
                scale(sign_value::<T>(s_ij).neg(), basis(k_ij)),
                scale(sign_value(-s_ij), basis(k_ij)),
            );
            // LHS ≡ scale(sv(-s_ij), basis(k_ij))
            // RHS ≡ scale(sv(s_ji), basis(k_ji))
            // When i≠j: s_ji = -s_ij, k_ji = k_ij → same expression
            Quat::<T>::axiom_eqv_symmetric(
                mul(conjugate(bj), conjugate(bi)),
                scale(sign_value(s_ji), basis(k_ji)),
            );
            Quat::<T>::axiom_eqv_transitive(
                conjugate(mul(bi, bj)),
                scale(sign_value(-s_ij), basis(k_ij)),
                mul(conjugate(bj), conjugate(bi)),
            );
        }
    }
}

// ===========================================================================
// Linear lifting: right
// ===========================================================================

proof fn lemma_conj_mul_rev_linear_right_add<T: Ring>(a: Quat<T>, b1: Quat<T>, b2: Quat<T>)
    requires conj_mul_rev(a, b1), conj_mul_rev(a, b2),
    ensures conj_mul_rev(a, b1.add(b2)),
{
    let ca = conjugate(a);
    // LHS: conj(mul(a, b1+b2)) ≡ conj(mul(a,b1)) + conj(mul(a,b2))
    //   ≡ mul(conj(b1),ca) + mul(conj(b2),ca)
    lemma_mul_distributes_right(a, b1, b2);
    lemma_conjugate_congruence(mul(a, b1.add(b2)), mul(a, b1).add(mul(a, b2)));
    lemma_conjugate_add(mul(a, b1), mul(a, b2));
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(a, b1.add(b2))),
        conjugate(mul(a, b1).add(mul(a, b2))),
        conjugate(mul(a, b1)).add(conjugate(mul(a, b2))),
    );
    additive_group_lemmas::lemma_add_congruence::<Quat<T>>(
        conjugate(mul(a, b1)), mul(conjugate(b1), ca),
        conjugate(mul(a, b2)), mul(conjugate(b2), ca),
    );
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(a, b1.add(b2))),
        conjugate(mul(a, b1)).add(conjugate(mul(a, b2))),
        mul(conjugate(b1), ca).add(mul(conjugate(b2), ca)),
    );
    // RHS: mul(conj(b1+b2), ca) ≡ mul(conj(b1)+conj(b2), ca) ≡ same
    lemma_conjugate_add(b1, b2);
    lemma_mul_congruence_left(conjugate(b1.add(b2)), conjugate(b1).add(conjugate(b2)), ca);
    lemma_mul_distributes_left(conjugate(b1), conjugate(b2), ca);
    Quat::<T>::axiom_eqv_transitive(
        mul(conjugate(b1.add(b2)), ca),
        mul(conjugate(b1).add(conjugate(b2)), ca),
        mul(conjugate(b1), ca).add(mul(conjugate(b2), ca)),
    );
    // Connect
    Quat::<T>::axiom_eqv_symmetric(
        mul(conjugate(b1.add(b2)), ca),
        mul(conjugate(b1), ca).add(mul(conjugate(b2), ca)),
    );
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(a, b1.add(b2))),
        mul(conjugate(b1), ca).add(mul(conjugate(b2), ca)),
        mul(conjugate(b1.add(b2)), ca),
    );
}

proof fn lemma_conj_mul_rev_linear_right_scale<T: Ring>(a: Quat<T>, b: Quat<T>, k: T)
    requires conj_mul_rev(a, b),
    ensures conj_mul_rev(a, scale(k, b)),
{
    let ca = conjugate(a);
    // LHS: conj(mul(a, scale(k,b))) ≡ scale(k, conj(mul(a,b))) ≡ scale(k, mul(conj(b),ca))
    lemma_mul_scale_right(a, k, b);
    lemma_conjugate_congruence(mul(a, scale(k, b)), scale(k, mul(a, b)));
    lemma_conjugate_scale(k, mul(a, b));
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(a, scale(k, b))),
        conjugate(scale(k, mul(a, b))),
        scale(k, conjugate(mul(a, b))),
    );
    lemma_scale_congruence(k, conjugate(mul(a, b)), mul(conjugate(b), ca));
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(a, scale(k, b))),
        scale(k, conjugate(mul(a, b))),
        scale(k, mul(conjugate(b), ca)),
    );
    // RHS: mul(conj(scale(k,b)), ca) ≡ mul(scale(k,conj(b)), ca) ≡ scale(k, mul(conj(b),ca))
    lemma_conjugate_scale(k, b);
    lemma_mul_congruence_left(conjugate(scale(k, b)), scale(k, conjugate(b)), ca);
    lemma_mul_scale_left(k, conjugate(b), ca);
    Quat::<T>::axiom_eqv_transitive(
        mul(conjugate(scale(k, b)), ca),
        mul(scale(k, conjugate(b)), ca),
        scale(k, mul(conjugate(b), ca)),
    );
    // Connect
    Quat::<T>::axiom_eqv_symmetric(
        mul(conjugate(scale(k, b)), ca),
        scale(k, mul(conjugate(b), ca)),
    );
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(a, scale(k, b))),
        scale(k, mul(conjugate(b), ca)),
        mul(conjugate(scale(k, b)), ca),
    );
}

// ===========================================================================
// Linear lifting: left
// ===========================================================================

proof fn lemma_conj_mul_rev_linear_left_add<T: Ring>(a1: Quat<T>, a2: Quat<T>, b: Quat<T>)
    requires conj_mul_rev(a1, b), conj_mul_rev(a2, b),
    ensures conj_mul_rev(a1.add(a2), b),
{
    let cb = conjugate(b);
    // LHS chain
    lemma_mul_distributes_left(a1, a2, b);
    lemma_conjugate_congruence(mul(a1.add(a2), b), mul(a1, b).add(mul(a2, b)));
    lemma_conjugate_add(mul(a1, b), mul(a2, b));
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(a1.add(a2), b)),
        conjugate(mul(a1, b).add(mul(a2, b))),
        conjugate(mul(a1, b)).add(conjugate(mul(a2, b))),
    );
    additive_group_lemmas::lemma_add_congruence::<Quat<T>>(
        conjugate(mul(a1, b)), mul(cb, conjugate(a1)),
        conjugate(mul(a2, b)), mul(cb, conjugate(a2)),
    );
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(a1.add(a2), b)),
        conjugate(mul(a1, b)).add(conjugate(mul(a2, b))),
        mul(cb, conjugate(a1)).add(mul(cb, conjugate(a2))),
    );
    // RHS chain
    lemma_conjugate_add(a1, a2);
    lemma_mul_congruence_right(cb, conjugate(a1.add(a2)), conjugate(a1).add(conjugate(a2)));
    lemma_mul_distributes_right(cb, conjugate(a1), conjugate(a2));
    Quat::<T>::axiom_eqv_transitive(
        mul(cb, conjugate(a1.add(a2))),
        mul(cb, conjugate(a1).add(conjugate(a2))),
        mul(cb, conjugate(a1)).add(mul(cb, conjugate(a2))),
    );
    // Connect
    Quat::<T>::axiom_eqv_symmetric(
        mul(cb, conjugate(a1.add(a2))),
        mul(cb, conjugate(a1)).add(mul(cb, conjugate(a2))),
    );
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(a1.add(a2), b)),
        mul(cb, conjugate(a1)).add(mul(cb, conjugate(a2))),
        mul(cb, conjugate(a1.add(a2))),
    );
}

proof fn lemma_conj_mul_rev_linear_left_scale<T: Ring>(a: Quat<T>, b: Quat<T>, k: T)
    requires conj_mul_rev(a, b),
    ensures conj_mul_rev(scale(k, a), b),
{
    let cb = conjugate(b);
    // LHS chain
    lemma_mul_scale_left(k, a, b);
    lemma_conjugate_congruence(mul(scale(k, a), b), scale(k, mul(a, b)));
    lemma_conjugate_scale(k, mul(a, b));
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(scale(k, a), b)),
        conjugate(scale(k, mul(a, b))),
        scale(k, conjugate(mul(a, b))),
    );
    lemma_scale_congruence(k, conjugate(mul(a, b)), mul(cb, conjugate(a)));
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(scale(k, a), b)),
        scale(k, conjugate(mul(a, b))),
        scale(k, mul(cb, conjugate(a))),
    );
    // RHS chain
    lemma_conjugate_scale(k, a);
    lemma_mul_congruence_right(cb, conjugate(scale(k, a)), scale(k, conjugate(a)));
    lemma_mul_scale_right(cb, k, conjugate(a));
    Quat::<T>::axiom_eqv_transitive(
        mul(cb, conjugate(scale(k, a))),
        mul(cb, scale(k, conjugate(a))),
        scale(k, mul(cb, conjugate(a))),
    );
    // Connect
    Quat::<T>::axiom_eqv_symmetric(
        mul(cb, conjugate(scale(k, a))),
        scale(k, mul(cb, conjugate(a))),
    );
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(scale(k, a), b)),
        scale(k, mul(cb, conjugate(a))),
        mul(cb, conjugate(scale(k, a))),
    );
}

// ===========================================================================
// Equivalence transfer
// ===========================================================================

proof fn lemma_conj_mul_rev_eqv_right<T: Ring>(a: Quat<T>, b1: Quat<T>, b2: Quat<T>)
    requires conj_mul_rev(a, b1), b1.eqv(b2),
    ensures conj_mul_rev(a, b2),
{
    let ca = conjugate(a);
    lemma_mul_congruence_right(a, b1, b2);
    Quat::<T>::axiom_eqv_symmetric(mul(a, b1), mul(a, b2));
    lemma_conjugate_congruence(mul(a, b2), mul(a, b1));
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(a, b2)), conjugate(mul(a, b1)), mul(conjugate(b1), ca),
    );
    lemma_conjugate_congruence(b1, b2);
    lemma_mul_congruence_left(conjugate(b1), conjugate(b2), ca);
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(a, b2)), mul(conjugate(b1), ca), mul(conjugate(b2), ca),
    );
}

proof fn lemma_conj_mul_rev_eqv_left<T: Ring>(a1: Quat<T>, a2: Quat<T>, b: Quat<T>)
    requires conj_mul_rev(a1, b), a1.eqv(a2),
    ensures conj_mul_rev(a2, b),
{
    let cb = conjugate(b);
    lemma_mul_congruence_left(a1, a2, b);
    Quat::<T>::axiom_eqv_symmetric(mul(a1, b), mul(a2, b));
    lemma_conjugate_congruence(mul(a2, b), mul(a1, b));
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(a2, b)), conjugate(mul(a1, b)), mul(cb, conjugate(a1)),
    );
    lemma_conjugate_congruence(a1, a2);
    lemma_mul_congruence_right(cb, conjugate(a1), conjugate(a2));
    Quat::<T>::axiom_eqv_transitive(
        conjugate(mul(a2, b)), mul(cb, conjugate(a1)), mul(cb, conjugate(a2)),
    );
}

// ===========================================================================
// Assembly
// ===========================================================================

proof fn lemma_linearize_right<T: Ring>(a: Quat<T>, b: Quat<T>)
    requires forall|j: int| 0 <= j < 4 ==> conj_mul_rev::<T>(a, basis(j)),
    ensures conj_mul_rev(a, b),
{
    lemma_conj_mul_rev_linear_right_scale(a, basis(0), b.w);
    lemma_conj_mul_rev_linear_right_scale(a, basis(1), b.x);
    lemma_conj_mul_rev_linear_right_scale(a, basis(2), b.y);
    lemma_conj_mul_rev_linear_right_scale(a, basis(3), b.z);
    lemma_conj_mul_rev_linear_right_add(a, scale(b.w, basis(0)), scale(b.x, basis(1)));
    lemma_conj_mul_rev_linear_right_add(a,
        scale(b.w, basis(0)).add(scale(b.x, basis(1))),
        scale(b.y, basis(2)),
    );
    lemma_conj_mul_rev_linear_right_add(a,
        scale(b.w, basis(0)).add(scale(b.x, basis(1))).add(scale(b.y, basis(2))),
        scale(b.z, basis(3)),
    );
    lemma_basis_decompose_eqv(b);
    Quat::<T>::axiom_eqv_symmetric(b, basis_decompose(b));
    lemma_conj_mul_rev_eqv_right(a, basis_decompose(b), b);
}

proof fn lemma_conj_basis_any<T: Ring>(i: int, b: Quat<T>)
    requires 0 <= i < 4,
    ensures conj_mul_rev::<T>(basis(i), b),
{
    lemma_conj_mul_rev_basis::<T>(i, 0);
    lemma_conj_mul_rev_basis::<T>(i, 1);
    lemma_conj_mul_rev_basis::<T>(i, 2);
    lemma_conj_mul_rev_basis::<T>(i, 3);
    lemma_linearize_right(basis(i), b);
}

/// Top-level: conj(a*b) ≡ conj(b)*conj(a)
pub proof fn lemma_conjugate_mul_reverse<T: Ring>(a: Quat<T>, b: Quat<T>)
    ensures conj_mul_rev(a, b),
{
    lemma_conj_basis_any::<T>(0, b);
    lemma_conj_basis_any::<T>(1, b);
    lemma_conj_basis_any::<T>(2, b);
    lemma_conj_basis_any::<T>(3, b);
    // Linearize left
    lemma_conj_mul_rev_linear_left_scale(basis(0), b, a.w);
    lemma_conj_mul_rev_linear_left_scale(basis(1), b, a.x);
    lemma_conj_mul_rev_linear_left_scale(basis(2), b, a.y);
    lemma_conj_mul_rev_linear_left_scale(basis(3), b, a.z);
    lemma_conj_mul_rev_linear_left_add(scale(a.w, basis(0)), scale(a.x, basis(1)), b);
    lemma_conj_mul_rev_linear_left_add(
        scale(a.w, basis(0)).add(scale(a.x, basis(1))),
        scale(a.y, basis(2)),
        b,
    );
    lemma_conj_mul_rev_linear_left_add(
        scale(a.w, basis(0)).add(scale(a.x, basis(1))).add(scale(a.y, basis(2))),
        scale(a.z, basis(3)),
        b,
    );
    lemma_basis_decompose_eqv(a);
    Quat::<T>::axiom_eqv_symmetric(a, basis_decompose(a));
    lemma_conj_mul_rev_eqv_left(basis_decompose(a), a, b);
}

} // verus!
