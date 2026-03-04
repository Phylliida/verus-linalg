use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use super::Quat;
use super::ops::*;
#[allow(unused_imports)]
use super::ops::mul;

verus! {

// ===========================================================================
// Spec functions for basis multiplication table
// ===========================================================================

/// Map integer sign to Ring element: 1 → one(), -1 → one().neg()
pub open spec fn sign_value<T: Ring>(sign: int) -> T {
    if sign == 1 { T::one() } else { T::one().neg() }
}

/// Result sign of basis(i)*basis(j) as integer: +1 or -1
pub open spec fn basis_mul_sign(i: int, j: int) -> int
    recommends 0 <= i < 4 && 0 <= j < 4,
{
    if i == 0 || j == 0 { 1 }
    else if i == j { -1 }
    else if (i == 1 && j == 2) || (i == 2 && j == 3) || (i == 3 && j == 1) { 1 }
    else { -1 }
}

/// Result index of basis(i)*basis(j): which basis element
pub open spec fn basis_mul_idx(i: int, j: int) -> int
    recommends 0 <= i < 4 && 0 <= j < 4,
{
    if i == 0 { j }
    else if j == 0 { i }
    else if i == j { 0 }
    else if (i == 1 && j == 2) || (i == 2 && j == 1) { 3 }
    else if (i == 2 && j == 3) || (i == 3 && j == 2) { 1 }
    else { 2 } // (1,3) or (3,1)
}

// ===========================================================================
// Scalar-level helpers
// ===========================================================================

/// 0 - a ≡ a.neg()
proof fn lemma_zero_sub<T: Ring>(a: T)
    ensures T::zero().sub(a).eqv(a.neg()),
{
    T::axiom_sub_is_add_neg(T::zero(), a);
    additive_group_lemmas::lemma_add_zero_left::<T>(a.neg());
    T::axiom_eqv_transitive(T::zero().sub(a), T::zero().add(a.neg()), a.neg());
}

/// Establish all needed facts about products of zero and one
proof fn lemma_zero_one_mul<T: Ring>()
    ensures
        T::zero().mul(T::zero()).eqv(T::zero()),
        T::zero().mul(T::one()).eqv(T::zero()),
        T::one().mul(T::zero()).eqv(T::zero()),
        T::one().mul(T::one()).eqv(T::one()),
        T::one().neg().mul(T::zero()).eqv(T::zero()),
        T::one().neg().mul(T::one()).eqv(T::one().neg()),
        T::one().mul(T::one().neg()).eqv(T::one().neg()),
{
    ring_lemmas::lemma_mul_zero_left::<T>(T::zero());
    ring_lemmas::lemma_mul_zero_left::<T>(T::one());
    T::axiom_mul_zero_right(T::one());
    T::axiom_mul_one_right(T::one());
    T::axiom_mul_zero_right(T::one().neg());
    ring_lemmas::lemma_mul_neg_one::<T>(T::one());
    ring_lemmas::lemma_mul_one_left::<T>(T::one().neg());
}

// ===========================================================================
// 4-way congruence helpers
// ===========================================================================

/// a1-b1-c1-d1 ≡ a2-b2-c2-d2 when components match
proof fn lemma_ssss_cong<T: Ring>(a1: T, a2: T, b1: T, b2: T, c1: T, c2: T, d1: T, d2: T)
    requires a1.eqv(a2), b1.eqv(b2), c1.eqv(c2), d1.eqv(d2),
    ensures a1.sub(b1).sub(c1).sub(d1).eqv(a2.sub(b2).sub(c2).sub(d2)),
{
    additive_group_lemmas::lemma_sub_congruence::<T>(a1, a2, b1, b2);
    additive_group_lemmas::lemma_sub_congruence::<T>(a1.sub(b1), a2.sub(b2), c1, c2);
    additive_group_lemmas::lemma_sub_congruence::<T>(a1.sub(b1).sub(c1), a2.sub(b2).sub(c2), d1, d2);
}

/// a1+b1+c1-d1 ≡ a2+b2+c2-d2
proof fn lemma_aas_cong<T: Ring>(a1: T, a2: T, b1: T, b2: T, c1: T, c2: T, d1: T, d2: T)
    requires a1.eqv(a2), b1.eqv(b2), c1.eqv(c2), d1.eqv(d2),
    ensures a1.add(b1).add(c1).sub(d1).eqv(a2.add(b2).add(c2).sub(d2)),
{
    additive_group_lemmas::lemma_add_congruence::<T>(a1, a2, b1, b2);
    additive_group_lemmas::lemma_add_congruence::<T>(a1.add(b1), a2.add(b2), c1, c2);
    additive_group_lemmas::lemma_sub_congruence::<T>(a1.add(b1).add(c1), a2.add(b2).add(c2), d1, d2);
}

/// a1-b1+c1+d1 ≡ a2-b2+c2+d2
proof fn lemma_saa_cong<T: Ring>(a1: T, a2: T, b1: T, b2: T, c1: T, c2: T, d1: T, d2: T)
    requires a1.eqv(a2), b1.eqv(b2), c1.eqv(c2), d1.eqv(d2),
    ensures a1.sub(b1).add(c1).add(d1).eqv(a2.sub(b2).add(c2).add(d2)),
{
    additive_group_lemmas::lemma_sub_congruence::<T>(a1, a2, b1, b2);
    additive_group_lemmas::lemma_add_congruence::<T>(a1.sub(b1), a2.sub(b2), c1, c2);
    additive_group_lemmas::lemma_add_congruence::<T>(a1.sub(b1).add(c1), a2.sub(b2).add(c2), d1, d2);
}

/// a1+b1-c1+d1 ≡ a2+b2-c2+d2
proof fn lemma_asa_cong<T: Ring>(a1: T, a2: T, b1: T, b2: T, c1: T, c2: T, d1: T, d2: T)
    requires a1.eqv(a2), b1.eqv(b2), c1.eqv(c2), d1.eqv(d2),
    ensures a1.add(b1).sub(c1).add(d1).eqv(a2.add(b2).sub(c2).add(d2)),
{
    additive_group_lemmas::lemma_add_congruence::<T>(a1, a2, b1, b2);
    additive_group_lemmas::lemma_sub_congruence::<T>(a1.add(b1), a2.add(b2), c1, c2);
    additive_group_lemmas::lemma_add_congruence::<T>(a1.add(b1).sub(c1), a2.add(b2).sub(c2), d1, d2);
}

// ===========================================================================
// All-zero simplification helpers
// ===========================================================================

/// 0-0-0-0 ≡ 0
proof fn lemma_ssss_zero<T: Ring>()
    ensures T::zero().sub(T::zero()).sub(T::zero()).sub(T::zero()).eqv(T::zero()),
{
    let z = T::zero();
    lemma_sub_zero::<T>(z);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.sub(z), z, z, z);
    T::axiom_eqv_transitive(z.sub(z).sub(z), z.sub(z), z);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.sub(z).sub(z), z, z, z);
    T::axiom_eqv_transitive(z.sub(z).sub(z).sub(z), z.sub(z), z);
}

/// 0+0+0-0 ≡ 0
proof fn lemma_aas_zero<T: Ring>()
    ensures T::zero().add(T::zero()).add(T::zero()).sub(T::zero()).eqv(T::zero()),
{
    let z = T::zero();
    T::axiom_add_zero_right(z);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_add_congruence::<T>(z.add(z), z, z, z);
    T::axiom_eqv_transitive(z.add(z).add(z), z.add(z), z);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.add(z).add(z), z, z, z);
    lemma_sub_zero::<T>(z);
    T::axiom_eqv_transitive(z.add(z).add(z).sub(z), z.sub(z), z);
}

/// 0-0+0+0 ≡ 0
proof fn lemma_saa_zero<T: Ring>()
    ensures T::zero().sub(T::zero()).add(T::zero()).add(T::zero()).eqv(T::zero()),
{
    let z = T::zero();
    lemma_sub_zero::<T>(z);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_add_congruence::<T>(z.sub(z), z, z, z);
    T::axiom_add_zero_right(z);
    T::axiom_eqv_transitive(z.sub(z).add(z), z.add(z), z);
    additive_group_lemmas::lemma_add_congruence::<T>(z.sub(z).add(z), z, z, z);
    T::axiom_eqv_transitive(z.sub(z).add(z).add(z), z.add(z), z);
}

/// 0+0-0+0 ≡ 0
proof fn lemma_asa_zero<T: Ring>()
    ensures T::zero().add(T::zero()).sub(T::zero()).add(T::zero()).eqv(T::zero()),
{
    let z = T::zero();
    T::axiom_add_zero_right(z);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.add(z), z, z, z);
    lemma_sub_zero::<T>(z);
    T::axiom_eqv_transitive(z.add(z).sub(z), z.sub(z), z);
    additive_group_lemmas::lemma_add_congruence::<T>(z.add(z).sub(z), z, z, z);
    T::axiom_add_zero_right(z);
    T::axiom_eqv_transitive(z.add(z).sub(z).add(z), z.add(z), z);
}

// ===========================================================================
// Non-zero simplification helpers (one non-zero term in 4-term expression)
// ===========================================================================

// --- ssss pattern: a-b-c-d ---

/// 0-1-0-0 ≡ -1  (for i*i w-component)
proof fn lemma_ssss_at1<T: Ring>()
    ensures T::zero().sub(T::one()).sub(T::zero()).sub(T::zero()).eqv(T::one().neg()),
{
    let z = T::zero(); let o = T::one(); let n = o.neg();
    lemma_zero_sub::<T>(o);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.sub(o), n, z, z);
    lemma_sub_zero::<T>(n);
    T::axiom_eqv_transitive(z.sub(o).sub(z), n.sub(z), n);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.sub(o).sub(z), n, z, z);
    T::axiom_eqv_transitive(z.sub(o).sub(z).sub(z), n.sub(z), n);
}

/// 0-0-1-0 ≡ -1  (for j*j w-component)
proof fn lemma_ssss_at2<T: Ring>()
    ensures T::zero().sub(T::zero()).sub(T::one()).sub(T::zero()).eqv(T::one().neg()),
{
    let z = T::zero(); let o = T::one(); let n = o.neg();
    lemma_sub_zero::<T>(z);
    T::axiom_eqv_reflexive(o);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.sub(z), z, o, o);
    lemma_zero_sub::<T>(o);
    T::axiom_eqv_transitive(z.sub(z).sub(o), z.sub(o), n);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.sub(z).sub(o), n, z, z);
    lemma_sub_zero::<T>(n);
    T::axiom_eqv_transitive(z.sub(z).sub(o).sub(z), n.sub(z), n);
}

/// 0-0-0-1 ≡ -1  (for k*k w-component)
proof fn lemma_ssss_at3<T: Ring>()
    ensures T::zero().sub(T::zero()).sub(T::zero()).sub(T::one()).eqv(T::one().neg()),
{
    let z = T::zero(); let o = T::one(); let n = o.neg();
    lemma_sub_zero::<T>(z);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.sub(z), z, z, z);
    T::axiom_eqv_transitive(z.sub(z).sub(z), z.sub(z), z);
    T::axiom_eqv_reflexive(o);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.sub(z).sub(z), z, o, o);
    lemma_zero_sub::<T>(o);
    T::axiom_eqv_transitive(z.sub(z).sub(z).sub(o), z.sub(o), n);
}

// --- aas pattern: a+b+c-d ---

/// 0+0+1-0 ≡ 1  (for j*k x-component)
proof fn lemma_aas_at2<T: Ring>()
    ensures T::zero().add(T::zero()).add(T::one()).sub(T::zero()).eqv(T::one()),
{
    let z = T::zero(); let o = T::one();
    T::axiom_add_zero_right(z);
    T::axiom_eqv_reflexive(o);
    additive_group_lemmas::lemma_add_congruence::<T>(z.add(z), z, o, o);
    additive_group_lemmas::lemma_add_zero_left::<T>(o);
    T::axiom_eqv_transitive(z.add(z).add(o), z.add(o), o);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.add(z).add(o), o, z, z);
    lemma_sub_zero::<T>(o);
    T::axiom_eqv_transitive(z.add(z).add(o).sub(z), o.sub(z), o);
}

/// 0+0+0-1 ≡ -1  (for k*j x-component)
proof fn lemma_aas_at3<T: Ring>()
    ensures T::zero().add(T::zero()).add(T::zero()).sub(T::one()).eqv(T::one().neg()),
{
    let z = T::zero(); let o = T::one(); let n = o.neg();
    T::axiom_add_zero_right(z);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_add_congruence::<T>(z.add(z), z, z, z);
    T::axiom_eqv_transitive(z.add(z).add(z), z.add(z), z);
    T::axiom_eqv_reflexive(o);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.add(z).add(z), z, o, o);
    lemma_zero_sub::<T>(o);
    T::axiom_eqv_transitive(z.add(z).add(z).sub(o), z.sub(o), n);
}

// --- saa pattern: a-b+c+d ---

/// 0-1+0+0 ≡ -1  (for i*k y-component)
proof fn lemma_saa_at1<T: Ring>()
    ensures T::zero().sub(T::one()).add(T::zero()).add(T::zero()).eqv(T::one().neg()),
{
    let z = T::zero(); let o = T::one(); let n = o.neg();
    lemma_zero_sub::<T>(o);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_add_congruence::<T>(z.sub(o), n, z, z);
    T::axiom_add_zero_right(n);
    T::axiom_eqv_transitive(z.sub(o).add(z), n.add(z), n);
    additive_group_lemmas::lemma_add_congruence::<T>(z.sub(o).add(z), n, z, z);
    T::axiom_eqv_transitive(z.sub(o).add(z).add(z), n.add(z), n);
}

/// 0-0+0+1 ≡ 1  (for k*i y-component)
proof fn lemma_saa_at3<T: Ring>()
    ensures T::zero().sub(T::zero()).add(T::zero()).add(T::one()).eqv(T::one()),
{
    let z = T::zero(); let o = T::one();
    lemma_sub_zero::<T>(z);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_add_congruence::<T>(z.sub(z), z, z, z);
    T::axiom_add_zero_right(z);
    T::axiom_eqv_transitive(z.sub(z).add(z), z.add(z), z);
    T::axiom_eqv_reflexive(o);
    additive_group_lemmas::lemma_add_congruence::<T>(z.sub(z).add(z), z, o, o);
    additive_group_lemmas::lemma_add_zero_left::<T>(o);
    T::axiom_eqv_transitive(z.sub(z).add(z).add(o), z.add(o), o);
}

// --- asa pattern: a+b-c+d ---

/// 0+1-0+0 ≡ 1  (for i*j z-component)
proof fn lemma_asa_at1<T: Ring>()
    ensures T::zero().add(T::one()).sub(T::zero()).add(T::zero()).eqv(T::one()),
{
    let z = T::zero(); let o = T::one();
    additive_group_lemmas::lemma_add_zero_left::<T>(o);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.add(o), o, z, z);
    lemma_sub_zero::<T>(o);
    T::axiom_eqv_transitive(z.add(o).sub(z), o.sub(z), o);
    additive_group_lemmas::lemma_add_congruence::<T>(z.add(o).sub(z), o, z, z);
    T::axiom_add_zero_right(o);
    T::axiom_eqv_transitive(z.add(o).sub(z).add(z), o.add(z), o);
}

/// 0+0-1+0 ≡ -1  (for j*i z-component)
proof fn lemma_asa_at2<T: Ring>()
    ensures T::zero().add(T::zero()).sub(T::one()).add(T::zero()).eqv(T::one().neg()),
{
    let z = T::zero(); let o = T::one(); let n = o.neg();
    T::axiom_add_zero_right(z);
    T::axiom_eqv_reflexive(o);
    additive_group_lemmas::lemma_sub_congruence::<T>(z.add(z), z, o, o);
    lemma_zero_sub::<T>(o);
    T::axiom_eqv_transitive(z.add(z).sub(o), z.sub(o), n);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_add_congruence::<T>(z.add(z).sub(o), n, z, z);
    T::axiom_add_zero_right(n);
    T::axiom_eqv_transitive(z.add(z).sub(o).add(z), n.add(z), n);
}

// ===========================================================================
// 9 non-trivial basis product lemmas
// ===========================================================================

/// Helper: prove one component eqv via intermediate value
/// Given lhs ≡ mid and rhs ≡ mid, proves lhs ≡ rhs
proof fn lemma_chain_via<T: Ring>(lhs: T, mid: T, rhs: T)
    requires lhs.eqv(mid), rhs.eqv(mid),
    ensures lhs.eqv(rhs),
{
    T::axiom_eqv_symmetric(rhs, mid);
    T::axiom_eqv_transitive(lhs, mid, rhs);
}

/// i*i = signed_basis(-1, 0)
proof fn lemma_basis_mul_11<T: Ring>()
    ensures mul(qi::<T>(), qi::<T>()).eqv(
        signed_basis(sign_value::<T>(basis_mul_sign(1, 1)), basis_mul_idx(1, 1))),
{
    lemma_zero_one_mul::<T>();
    let z = T::zero(); let o = T::one(); let n = o.neg();
    // Source: mul(qi, qi). Target: scale(-1, one()) = (-1*1, -1*0, -1*0, -1*0)
    // w: 0*0 - 1*1 - 0*0 - 0*0. Products: 0≡0, 1≡1, 0≡0, 0≡0.
    lemma_ssss_cong::<T>(z.mul(z), z, o.mul(o), o, z.mul(z), z, z.mul(z), z);
    lemma_ssss_at1::<T>();
    T::axiom_eqv_transitive(mul(qi::<T>(), qi::<T>()).w, z.sub(o).sub(z).sub(z), n);
    // Target w: (-1)*1 ≡ -1
    lemma_chain_via::<T>(mul(qi::<T>(), qi::<T>()).w, n, n.mul(o));
    // x: 0*1 + 1*0 + 0*0 - 0*0
    lemma_aas_cong::<T>(z.mul(o), z, o.mul(z), z, z.mul(z), z, z.mul(z), z);
    lemma_aas_zero::<T>();
    T::axiom_eqv_transitive(mul(qi::<T>(), qi::<T>()).x, z.add(z).add(z).sub(z), z);
    // Target x: (-1)*0 ≡ 0
    lemma_chain_via::<T>(mul(qi::<T>(), qi::<T>()).x, z, n.mul(z));
    // y: 0*0 - 1*0 + 0*0 + 0*1
    lemma_saa_cong::<T>(z.mul(z), z, o.mul(z), z, z.mul(z), z, z.mul(o), z);
    lemma_saa_zero::<T>();
    T::axiom_eqv_transitive(mul(qi::<T>(), qi::<T>()).y, z.sub(z).add(z).add(z), z);
    lemma_chain_via::<T>(mul(qi::<T>(), qi::<T>()).y, z, n.mul(z));
    // z: 0*0 + 1*0 - 0*1 + 0*0
    lemma_asa_cong::<T>(z.mul(z), z, o.mul(z), z, z.mul(o), z, z.mul(z), z);
    lemma_asa_zero::<T>();
    T::axiom_eqv_transitive(mul(qi::<T>(), qi::<T>()).z, z.add(z).sub(z).add(z), z);
    lemma_chain_via::<T>(mul(qi::<T>(), qi::<T>()).z, z, n.mul(z));
}

/// j*j = signed_basis(-1, 0)
proof fn lemma_basis_mul_22<T: Ring>()
    ensures mul(qj::<T>(), qj::<T>()).eqv(
        signed_basis(sign_value::<T>(basis_mul_sign(2, 2)), basis_mul_idx(2, 2))),
{
    lemma_zero_one_mul::<T>();
    let z = T::zero(); let o = T::one(); let n = o.neg();
    // w: 0*0 - 0*0 - 1*1 - 0*0
    lemma_ssss_cong::<T>(z.mul(z), z, z.mul(z), z, o.mul(o), o, z.mul(z), z);
    lemma_ssss_at2::<T>();
    T::axiom_eqv_transitive(mul(qj::<T>(), qj::<T>()).w, z.sub(z).sub(o).sub(z), n);
    lemma_chain_via::<T>(mul(qj::<T>(), qj::<T>()).w, n, n.mul(o));
    // x: 0*0 + 0*0 + 1*0 - 0*1
    lemma_aas_cong::<T>(z.mul(z), z, z.mul(z), z, o.mul(z), z, z.mul(o), z);
    lemma_aas_zero::<T>();
    T::axiom_eqv_transitive(mul(qj::<T>(), qj::<T>()).x, z.add(z).add(z).sub(z), z);
    lemma_chain_via::<T>(mul(qj::<T>(), qj::<T>()).x, z, n.mul(z));
    // y: 0*1 - 0*0 + 1*0 + 0*0
    lemma_saa_cong::<T>(z.mul(o), z, z.mul(z), z, o.mul(z), z, z.mul(z), z);
    lemma_saa_zero::<T>();
    T::axiom_eqv_transitive(mul(qj::<T>(), qj::<T>()).y, z.sub(z).add(z).add(z), z);
    lemma_chain_via::<T>(mul(qj::<T>(), qj::<T>()).y, z, n.mul(z));
    // z: 0*0 + 0*0 - 1*0 + 0*0
    lemma_asa_cong::<T>(z.mul(z), z, z.mul(o), z, o.mul(z), z, z.mul(z), z);
    lemma_asa_zero::<T>();
    T::axiom_eqv_transitive(mul(qj::<T>(), qj::<T>()).z, z.add(z).sub(z).add(z), z);
    lemma_chain_via::<T>(mul(qj::<T>(), qj::<T>()).z, z, n.mul(z));
}

/// k*k = signed_basis(-1, 0)
proof fn lemma_basis_mul_33<T: Ring>()
    ensures mul(qk::<T>(), qk::<T>()).eqv(
        signed_basis(sign_value::<T>(basis_mul_sign(3, 3)), basis_mul_idx(3, 3))),
{
    lemma_zero_one_mul::<T>();
    let z = T::zero(); let o = T::one(); let n = o.neg();
    // w: 0*0 - 0*0 - 0*0 - 1*1
    lemma_ssss_cong::<T>(z.mul(z), z, z.mul(z), z, z.mul(z), z, o.mul(o), o);
    lemma_ssss_at3::<T>();
    T::axiom_eqv_transitive(mul(qk::<T>(), qk::<T>()).w, z.sub(z).sub(z).sub(o), n);
    lemma_chain_via::<T>(mul(qk::<T>(), qk::<T>()).w, n, n.mul(o));
    // x: 0*0 + 0*0 + 0*1 - 1*0
    lemma_aas_cong::<T>(z.mul(z), z, z.mul(z), z, z.mul(o), z, o.mul(z), z);
    lemma_aas_zero::<T>();
    T::axiom_eqv_transitive(mul(qk::<T>(), qk::<T>()).x, z.add(z).add(z).sub(z), z);
    lemma_chain_via::<T>(mul(qk::<T>(), qk::<T>()).x, z, n.mul(z));
    // y: 0*0 - 0*1 + 0*0 + 1*0
    lemma_saa_cong::<T>(z.mul(z), z, z.mul(o), z, z.mul(z), z, o.mul(z), z);
    lemma_saa_zero::<T>();
    T::axiom_eqv_transitive(mul(qk::<T>(), qk::<T>()).y, z.sub(z).add(z).add(z), z);
    lemma_chain_via::<T>(mul(qk::<T>(), qk::<T>()).y, z, n.mul(z));
    // z: 0*1 + 0*0 - 0*0 + 1*0
    lemma_asa_cong::<T>(z.mul(o), z, z.mul(z), z, z.mul(z), z, o.mul(z), z);
    lemma_asa_zero::<T>();
    T::axiom_eqv_transitive(mul(qk::<T>(), qk::<T>()).z, z.add(z).sub(z).add(z), z);
    lemma_chain_via::<T>(mul(qk::<T>(), qk::<T>()).z, z, n.mul(z));
}

/// i*j = k → signed_basis(1, 3)
proof fn lemma_basis_mul_12<T: Ring>()
    ensures mul(qi::<T>(), qj::<T>()).eqv(
        signed_basis(sign_value::<T>(basis_mul_sign(1, 2)), basis_mul_idx(1, 2))),
{
    lemma_zero_one_mul::<T>();
    let z = T::zero(); let o = T::one();
    // Target: scale(1, qk()) = (1*0, 1*0, 1*0, 1*1)
    // w: 0*0 - 1*0 - 0*1 - 0*0 → all zero
    lemma_ssss_cong::<T>(z.mul(z), z, o.mul(z), z, z.mul(o), z, z.mul(z), z);
    lemma_ssss_zero::<T>();
    T::axiom_eqv_transitive(mul(qi::<T>(), qj::<T>()).w, z.sub(z).sub(z).sub(z), z);
    lemma_chain_via::<T>(mul(qi::<T>(), qj::<T>()).w, z, o.mul(z));
    // x: 0*0 + 1*0 + 0*0 - 0*1 → all zero
    lemma_aas_cong::<T>(z.mul(z), z, o.mul(z), z, z.mul(z), z, z.mul(o), z);
    lemma_aas_zero::<T>();
    T::axiom_eqv_transitive(mul(qi::<T>(), qj::<T>()).x, z.add(z).add(z).sub(z), z);
    lemma_chain_via::<T>(mul(qi::<T>(), qj::<T>()).x, z, o.mul(z));
    // y: 0*1 - 1*0 + 0*0 + 0*0 → all zero
    lemma_saa_cong::<T>(z.mul(o), z, o.mul(z), z, z.mul(z), z, z.mul(z), z);
    lemma_saa_zero::<T>();
    T::axiom_eqv_transitive(mul(qi::<T>(), qj::<T>()).y, z.sub(z).add(z).add(z), z);
    lemma_chain_via::<T>(mul(qi::<T>(), qj::<T>()).y, z, o.mul(z));
    // z: 0*0 + 1*1 - 0*0 + 0*0 → 0+1-0+0 = 1
    lemma_asa_cong::<T>(z.mul(z), z, o.mul(o), o, z.mul(z), z, z.mul(z), z);
    lemma_asa_at1::<T>();
    T::axiom_eqv_transitive(mul(qi::<T>(), qj::<T>()).z, z.add(o).sub(z).add(z), o);
    lemma_chain_via::<T>(mul(qi::<T>(), qj::<T>()).z, o, o.mul(o));
}

/// j*k = i → signed_basis(1, 1)
proof fn lemma_basis_mul_23<T: Ring>()
    ensures mul(qj::<T>(), qk::<T>()).eqv(
        signed_basis(sign_value::<T>(basis_mul_sign(2, 3)), basis_mul_idx(2, 3))),
{
    lemma_zero_one_mul::<T>();
    let z = T::zero(); let o = T::one();
    // Target: scale(1, qi()) = (1*0, 1*1, 1*0, 1*0)
    // w: 0*0 - 0*0 - 1*0 - 0*1 → all zero
    lemma_ssss_cong::<T>(z.mul(z), z, z.mul(z), z, o.mul(z), z, z.mul(o), z);
    lemma_ssss_zero::<T>();
    T::axiom_eqv_transitive(mul(qj::<T>(), qk::<T>()).w, z.sub(z).sub(z).sub(z), z);
    lemma_chain_via::<T>(mul(qj::<T>(), qk::<T>()).w, z, o.mul(z));
    // x: 0*0 + 0*0 + 1*1 - 0*0 → 0+0+1-0 = 1
    lemma_aas_cong::<T>(z.mul(z), z, z.mul(z), z, o.mul(o), o, z.mul(z), z);
    lemma_aas_at2::<T>();
    T::axiom_eqv_transitive(mul(qj::<T>(), qk::<T>()).x, z.add(z).add(o).sub(z), o);
    lemma_chain_via::<T>(mul(qj::<T>(), qk::<T>()).x, o, o.mul(o));
    // y: 0*0 - 0*1 + 1*0 + 0*0 → all zero
    lemma_saa_cong::<T>(z.mul(z), z, z.mul(o), z, o.mul(z), z, z.mul(z), z);
    lemma_saa_zero::<T>();
    T::axiom_eqv_transitive(mul(qj::<T>(), qk::<T>()).y, z.sub(z).add(z).add(z), z);
    lemma_chain_via::<T>(mul(qj::<T>(), qk::<T>()).y, z, o.mul(z));
    // z: 0*1 + 0*0 - 1*0 + 0*0 → all zero
    lemma_asa_cong::<T>(z.mul(o), z, z.mul(z), z, o.mul(z), z, z.mul(z), z);
    lemma_asa_zero::<T>();
    T::axiom_eqv_transitive(mul(qj::<T>(), qk::<T>()).z, z.add(z).sub(z).add(z), z);
    lemma_chain_via::<T>(mul(qj::<T>(), qk::<T>()).z, z, o.mul(z));
}

/// k*i = j → signed_basis(1, 2)
proof fn lemma_basis_mul_31<T: Ring>()
    ensures mul(qk::<T>(), qi::<T>()).eqv(
        signed_basis(sign_value::<T>(basis_mul_sign(3, 1)), basis_mul_idx(3, 1))),
{
    lemma_zero_one_mul::<T>();
    let z = T::zero(); let o = T::one();
    // Target: scale(1, qj()) = (1*0, 1*0, 1*1, 1*0)
    // w: 0*0 - 0*1 - 0*0 - 1*0 → all zero
    lemma_ssss_cong::<T>(z.mul(z), z, z.mul(o), z, z.mul(z), z, o.mul(z), z);
    lemma_ssss_zero::<T>();
    T::axiom_eqv_transitive(mul(qk::<T>(), qi::<T>()).w, z.sub(z).sub(z).sub(z), z);
    lemma_chain_via::<T>(mul(qk::<T>(), qi::<T>()).w, z, o.mul(z));
    // x: 0*1 + 0*0 + 0*0 - 1*0 → all zero
    lemma_aas_cong::<T>(z.mul(o), z, z.mul(z), z, z.mul(z), z, o.mul(z), z);
    lemma_aas_zero::<T>();
    T::axiom_eqv_transitive(mul(qk::<T>(), qi::<T>()).x, z.add(z).add(z).sub(z), z);
    lemma_chain_via::<T>(mul(qk::<T>(), qi::<T>()).x, z, o.mul(z));
    // y: 0*0 - 0*0 + 0*0 + 1*1 → 0-0+0+1 = 1
    lemma_saa_cong::<T>(z.mul(z), z, z.mul(z), z, z.mul(z), z, o.mul(o), o);
    lemma_saa_at3::<T>();
    T::axiom_eqv_transitive(mul(qk::<T>(), qi::<T>()).y, z.sub(z).add(z).add(o), o);
    lemma_chain_via::<T>(mul(qk::<T>(), qi::<T>()).y, o, o.mul(o));
    // z: 0*0 + 0*0 - 0*1 + 1*0 → all zero
    lemma_asa_cong::<T>(z.mul(z), z, z.mul(z), z, z.mul(o), z, o.mul(z), z);
    lemma_asa_zero::<T>();
    T::axiom_eqv_transitive(mul(qk::<T>(), qi::<T>()).z, z.add(z).sub(z).add(z), z);
    lemma_chain_via::<T>(mul(qk::<T>(), qi::<T>()).z, z, o.mul(z));
}

/// j*i = -k → signed_basis(-1, 3)
proof fn lemma_basis_mul_21<T: Ring>()
    ensures mul(qj::<T>(), qi::<T>()).eqv(
        signed_basis(sign_value::<T>(basis_mul_sign(2, 1)), basis_mul_idx(2, 1))),
{
    lemma_zero_one_mul::<T>();
    let z = T::zero(); let o = T::one(); let n = o.neg();
    // Target: scale(-1, qk()) = (-1*0, -1*0, -1*0, -1*1)
    // w: 0*0 - 0*1 - 1*0 - 0*0 → all zero
    lemma_ssss_cong::<T>(z.mul(z), z, z.mul(o), z, o.mul(z), z, z.mul(z), z);
    lemma_ssss_zero::<T>();
    T::axiom_eqv_transitive(mul(qj::<T>(), qi::<T>()).w, z.sub(z).sub(z).sub(z), z);
    lemma_chain_via::<T>(mul(qj::<T>(), qi::<T>()).w, z, n.mul(z));
    // x: 0*1 + 0*0 + 1*0 - 0*0 → all zero
    lemma_aas_cong::<T>(z.mul(o), z, z.mul(z), z, o.mul(z), z, z.mul(z), z);
    lemma_aas_zero::<T>();
    T::axiom_eqv_transitive(mul(qj::<T>(), qi::<T>()).x, z.add(z).add(z).sub(z), z);
    lemma_chain_via::<T>(mul(qj::<T>(), qi::<T>()).x, z, n.mul(z));
    // y: 0*0 - 0*0 + 1*0 + 0*1 → all zero
    lemma_saa_cong::<T>(z.mul(z), z, z.mul(z), z, o.mul(z), z, z.mul(o), z);
    lemma_saa_zero::<T>();
    T::axiom_eqv_transitive(mul(qj::<T>(), qi::<T>()).y, z.sub(z).add(z).add(z), z);
    lemma_chain_via::<T>(mul(qj::<T>(), qi::<T>()).y, z, n.mul(z));
    // z: 0*0 + 0*0 - 1*1 + 0*0 → 0+0-1+0 = -1
    lemma_asa_cong::<T>(z.mul(z), z, z.mul(z), z, o.mul(o), o, z.mul(z), z);
    lemma_asa_at2::<T>();
    T::axiom_eqv_transitive(mul(qj::<T>(), qi::<T>()).z, z.add(z).sub(o).add(z), n);
    lemma_chain_via::<T>(mul(qj::<T>(), qi::<T>()).z, n, n.mul(o));
}

/// k*j = -i → signed_basis(-1, 1)
proof fn lemma_basis_mul_32<T: Ring>()
    ensures mul(qk::<T>(), qj::<T>()).eqv(
        signed_basis(sign_value::<T>(basis_mul_sign(3, 2)), basis_mul_idx(3, 2))),
{
    lemma_zero_one_mul::<T>();
    let z = T::zero(); let o = T::one(); let n = o.neg();
    // Target: scale(-1, qi()) = (-1*0, -1*1, -1*0, -1*0)
    // w: 0*0 - 0*0 - 0*1 - 1*0 → all zero
    lemma_ssss_cong::<T>(z.mul(z), z, z.mul(z), z, z.mul(o), z, o.mul(z), z);
    lemma_ssss_zero::<T>();
    T::axiom_eqv_transitive(mul(qk::<T>(), qj::<T>()).w, z.sub(z).sub(z).sub(z), z);
    lemma_chain_via::<T>(mul(qk::<T>(), qj::<T>()).w, z, n.mul(z));
    // x: 0*0 + 0*0 + 0*0 - 1*1 → 0+0+0-1 = -1
    lemma_aas_cong::<T>(z.mul(z), z, z.mul(z), z, z.mul(z), z, o.mul(o), o);
    lemma_aas_at3::<T>();
    T::axiom_eqv_transitive(mul(qk::<T>(), qj::<T>()).x, z.add(z).add(z).sub(o), n);
    lemma_chain_via::<T>(mul(qk::<T>(), qj::<T>()).x, n, n.mul(o));
    // y: 0*1 - 0*0 + 0*0 + 1*0 → all zero
    lemma_saa_cong::<T>(z.mul(o), z, z.mul(z), z, z.mul(z), z, o.mul(z), z);
    lemma_saa_zero::<T>();
    T::axiom_eqv_transitive(mul(qk::<T>(), qj::<T>()).y, z.sub(z).add(z).add(z), z);
    lemma_chain_via::<T>(mul(qk::<T>(), qj::<T>()).y, z, n.mul(z));
    // z: 0*0 + 0*1 - 0*0 + 1*0 → all zero
    lemma_asa_cong::<T>(z.mul(z), z, z.mul(o), z, z.mul(z), z, o.mul(z), z);
    lemma_asa_zero::<T>();
    T::axiom_eqv_transitive(mul(qk::<T>(), qj::<T>()).z, z.add(z).sub(z).add(z), z);
    lemma_chain_via::<T>(mul(qk::<T>(), qj::<T>()).z, z, n.mul(z));
}

/// i*k = -j → signed_basis(-1, 2)
proof fn lemma_basis_mul_13<T: Ring>()
    ensures mul(qi::<T>(), qk::<T>()).eqv(
        signed_basis(sign_value::<T>(basis_mul_sign(1, 3)), basis_mul_idx(1, 3))),
{
    lemma_zero_one_mul::<T>();
    let z = T::zero(); let o = T::one(); let n = o.neg();
    // Target: scale(-1, qj()) = (-1*0, -1*0, -1*1, -1*0)
    // w: 0*0 - 1*0 - 0*0 - 0*1 → all zero
    lemma_ssss_cong::<T>(z.mul(z), z, o.mul(z), z, z.mul(z), z, z.mul(o), z);
    lemma_ssss_zero::<T>();
    T::axiom_eqv_transitive(mul(qi::<T>(), qk::<T>()).w, z.sub(z).sub(z).sub(z), z);
    lemma_chain_via::<T>(mul(qi::<T>(), qk::<T>()).w, z, n.mul(z));
    // x: 0*0 + 1*0 + 0*1 - 0*0 → all zero
    lemma_aas_cong::<T>(z.mul(z), z, o.mul(z), z, z.mul(o), z, z.mul(z), z);
    lemma_aas_zero::<T>();
    T::axiom_eqv_transitive(mul(qi::<T>(), qk::<T>()).x, z.add(z).add(z).sub(z), z);
    lemma_chain_via::<T>(mul(qi::<T>(), qk::<T>()).x, z, n.mul(z));
    // y: 0*0 - 1*1 + 0*0 + 0*0 → 0-1+0+0 = -1
    lemma_saa_cong::<T>(z.mul(z), z, o.mul(o), o, z.mul(z), z, z.mul(z), z);
    lemma_saa_at1::<T>();
    T::axiom_eqv_transitive(mul(qi::<T>(), qk::<T>()).y, z.sub(o).add(z).add(z), n);
    lemma_chain_via::<T>(mul(qi::<T>(), qk::<T>()).y, n, n.mul(o));
    // z: 0*1 + 1*0 - 0*0 + 0*0 → all zero
    lemma_asa_cong::<T>(z.mul(o), z, o.mul(z), z, z.mul(z), z, z.mul(z), z);
    lemma_asa_zero::<T>();
    T::axiom_eqv_transitive(mul(qi::<T>(), qk::<T>()).z, z.add(z).sub(z).add(z), z);
    lemma_chain_via::<T>(mul(qi::<T>(), qk::<T>()).z, z, n.mul(z));
}

// ===========================================================================
// Master dispatcher: basis(i)*basis(j) ≡ signed_basis(sign_value(sign), idx)
// ===========================================================================

pub proof fn lemma_basis_mul_to_signed<T: Ring>(i: int, j: int)
    requires 0 <= i < 4, 0 <= j < 4,
    ensures mul(basis::<T>(i), basis::<T>(j)).eqv(
        signed_basis(sign_value::<T>(basis_mul_sign(i, j)), basis_mul_idx(i, j))),
{
    if i == 0 {
        // mul(one(), basis(j)) ≡ basis(j) ≡ scale(one(), basis(j))
        lemma_mul_one_left::<T>(basis(j));
        lemma_scale_identity::<T>(basis(j));
        Quat::<T>::axiom_eqv_symmetric(scale(T::one(), basis(j)), basis(j));
        Quat::<T>::axiom_eqv_transitive(
            mul(basis::<T>(i), basis::<T>(j)),
            basis(j),
            scale(T::one(), basis(j)),
        );
    } else if j == 0 {
        // mul(basis(i), one()) ≡ basis(i) ≡ scale(one(), basis(i))
        lemma_mul_one_right::<T>(basis(i));
        lemma_scale_identity::<T>(basis(i));
        Quat::<T>::axiom_eqv_symmetric(scale(T::one(), basis(i)), basis(i));
        Quat::<T>::axiom_eqv_transitive(
            mul(basis::<T>(i), basis::<T>(j)),
            basis(i),
            scale(T::one(), basis(i)),
        );
    } else if i == 1 && j == 1 { lemma_basis_mul_11::<T>(); }
    else if i == 2 && j == 2 { lemma_basis_mul_22::<T>(); }
    else if i == 3 && j == 3 { lemma_basis_mul_33::<T>(); }
    else if i == 1 && j == 2 { lemma_basis_mul_12::<T>(); }
    else if i == 2 && j == 3 { lemma_basis_mul_23::<T>(); }
    else if i == 3 && j == 1 { lemma_basis_mul_31::<T>(); }
    else if i == 2 && j == 1 { lemma_basis_mul_21::<T>(); }
    else if i == 3 && j == 2 { lemma_basis_mul_32::<T>(); }
    else { // i == 1 && j == 3
        lemma_basis_mul_13::<T>();
    }
}

// ===========================================================================
// Sign composition lemma
// ===========================================================================

/// sign_value(s1) * sign_value(s2) ≡ sign_value(s1 * s2)
pub proof fn lemma_sign_value_mul<T: Ring>(s1: int, s2: int)
    requires (s1 == 1 || s1 == -1) && (s2 == 1 || s2 == -1),
    ensures sign_value::<T>(s1).mul(sign_value::<T>(s2)).eqv(sign_value::<T>(s1 * s2)),
{
    if s1 == 1 && s2 == 1 {
        T::axiom_mul_one_right(T::one());
    } else if s1 == 1 && s2 == -1 {
        ring_lemmas::lemma_mul_one_left::<T>(T::one().neg());
    } else if s1 == -1 && s2 == 1 {
        T::axiom_mul_one_right(T::one().neg());
    } else {
        // (-1)*(-1) ≡ 1*1 ≡ 1
        ring_lemmas::lemma_neg_mul_neg::<T>(T::one(), T::one());
        T::axiom_mul_one_right(T::one());
        T::axiom_eqv_transitive(
            T::one().neg().mul(T::one().neg()),
            T::one().mul(T::one()),
            T::one(),
        );
    }
}

// ===========================================================================
// Basis associativity
// ===========================================================================

/// (basis(i)*basis(j))*basis(k) ≡ basis(i)*(basis(j)*basis(k))
pub proof fn lemma_basis_assoc_indices<T: Ring>(i: int, j: int, k: int)
    requires 0 <= i < 4, 0 <= j < 4, 0 <= k < 4,
    ensures mul(mul(basis::<T>(i), basis::<T>(j)), basis::<T>(k)).eqv(
                mul(basis::<T>(i), mul(basis::<T>(j), basis::<T>(k)))),
{
    let s_ij = basis_mul_sign(i, j);
    let m_ij = basis_mul_idx(i, j);
    let s_mk = basis_mul_sign(m_ij, k);
    let m_mk = basis_mul_idx(m_ij, k);

    let s_jk = basis_mul_sign(j, k);
    let m_jk = basis_mul_idx(j, k);
    let s_im = basis_mul_sign(i, m_jk);
    let m_im = basis_mul_idx(i, m_jk);

    let sv_ij = sign_value::<T>(s_ij);
    let sv_mk = sign_value::<T>(s_mk);
    let sv_jk = sign_value::<T>(s_jk);
    let sv_im = sign_value::<T>(s_im);

    // --- LHS chain ---
    // Step L1: basis(i)*basis(j) ≡ signed_basis(sv_ij, m_ij)
    lemma_basis_mul_to_signed::<T>(i, j);
    // Step L2: mul(basis(i)*basis(j), basis(k)) ≡ mul(signed_basis(...), basis(k))
    lemma_mul_congruence_left(
        mul(basis::<T>(i), basis::<T>(j)),
        signed_basis(sv_ij, m_ij),
        basis::<T>(k),
    );
    // Step L3: mul(scale(sv_ij, basis(m_ij)), basis(k)) ≡ scale(sv_ij, mul(basis(m_ij), basis(k)))
    lemma_mul_scale_left(sv_ij, basis::<T>(m_ij), basis::<T>(k));
    // Step L4: basis(m_ij)*basis(k) ≡ signed_basis(sv_mk, m_mk)
    lemma_basis_mul_to_signed::<T>(m_ij, k);
    // Step L5: scale(sv_ij, mul(basis(m_ij), basis(k))) ≡ scale(sv_ij, signed_basis(sv_mk, m_mk))
    lemma_scale_congruence(sv_ij, mul(basis::<T>(m_ij), basis::<T>(k)), signed_basis(sv_mk, m_mk));
    // Step L6: scale(sv_ij, scale(sv_mk, basis(m_mk))) ≡ scale(sv_ij.mul(sv_mk), basis(m_mk))
    lemma_scale_associative(sv_ij, sv_mk, basis::<T>(m_mk));

    // Chain: LHS ≡ mul(scale(sv_ij, basis(m_ij)), basis(k)) [L2]
    //            ≡ scale(sv_ij, mul(basis(m_ij), basis(k))) [L3]
    //            ≡ scale(sv_ij, scale(sv_mk, basis(m_mk))) [L5]
    //            ≡ scale(sv_ij.mul(sv_mk), basis(m_mk))    [L6]
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(basis::<T>(i), basis::<T>(j)), basis::<T>(k)),
        mul(scale(sv_ij, basis(m_ij)), basis(k)),
        scale(sv_ij, mul(basis(m_ij), basis(k))),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(basis::<T>(i), basis::<T>(j)), basis::<T>(k)),
        scale(sv_ij, mul(basis(m_ij), basis(k))),
        scale(sv_ij, scale(sv_mk, basis(m_mk))),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(basis::<T>(i), basis::<T>(j)), basis::<T>(k)),
        scale(sv_ij, scale(sv_mk, basis(m_mk))),
        scale(sv_ij.mul(sv_mk), basis(m_mk)),
    );

    // --- RHS chain ---
    // Step R1: basis(j)*basis(k) ≡ signed_basis(sv_jk, m_jk)
    lemma_basis_mul_to_signed::<T>(j, k);
    // Step R2: mul(basis(i), basis(j)*basis(k)) ≡ mul(basis(i), signed_basis(...))
    lemma_mul_congruence_right(
        basis::<T>(i),
        mul(basis::<T>(j), basis::<T>(k)),
        signed_basis(sv_jk, m_jk),
    );
    // Step R3: mul(basis(i), scale(sv_jk, basis(m_jk))) ≡ scale(sv_jk, mul(basis(i), basis(m_jk)))
    lemma_mul_scale_right(basis::<T>(i), sv_jk, basis::<T>(m_jk));
    // Step R4: basis(i)*basis(m_jk) ≡ signed_basis(sv_im, m_im)
    lemma_basis_mul_to_signed::<T>(i, m_jk);
    // Step R5: scale(sv_jk, mul(basis(i), basis(m_jk))) ≡ scale(sv_jk, signed_basis(sv_im, m_im))
    lemma_scale_congruence(sv_jk, mul(basis::<T>(i), basis::<T>(m_jk)), signed_basis(sv_im, m_im));
    // Step R6: scale(sv_jk, scale(sv_im, basis(m_im))) ≡ scale(sv_jk.mul(sv_im), basis(m_im))
    lemma_scale_associative(sv_jk, sv_im, basis::<T>(m_im));

    // Chain: RHS ≡ mul(basis(i), scale(sv_jk, basis(m_jk))) [R2]
    //            ≡ scale(sv_jk, mul(basis(i), basis(m_jk))) [R3]
    //            ≡ scale(sv_jk, scale(sv_im, basis(m_im))) [R5]
    //            ≡ scale(sv_jk.mul(sv_im), basis(m_im))    [R6]
    Quat::<T>::axiom_eqv_transitive(
        mul(basis::<T>(i), mul(basis::<T>(j), basis::<T>(k))),
        mul(basis::<T>(i), scale(sv_jk, basis(m_jk))),
        scale(sv_jk, mul(basis(i), basis(m_jk))),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(basis::<T>(i), mul(basis::<T>(j), basis::<T>(k))),
        scale(sv_jk, mul(basis(i), basis(m_jk))),
        scale(sv_jk, scale(sv_im, basis(m_im))),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(basis::<T>(i), mul(basis::<T>(j), basis::<T>(k))),
        scale(sv_jk, scale(sv_im, basis(m_im))),
        scale(sv_jk.mul(sv_im), basis(m_im)),
    );

    // --- Connect LHS and RHS ---
    // LHS ≡ scale(sv_ij.mul(sv_mk), basis(m_mk))
    // RHS ≡ scale(sv_jk.mul(sv_im), basis(m_im))
    // Need: these two are eqv.
    // m_mk == m_im (verified by SMT for all concrete i,j,k)
    // sv_ij.mul(sv_mk) ≡ sign_value(s_ij * s_mk) ≡ sign_value(s_jk * s_im) ≡ sv_jk.mul(sv_im)
    lemma_sign_value_mul::<T>(s_ij, s_mk);
    lemma_sign_value_mul::<T>(s_jk, s_im);
    // s_ij * s_mk == s_jk * s_im (integer, SMT verifies)
    // So sign_value(s_ij * s_mk) == sign_value(s_jk * s_im) definitionally
    T::axiom_eqv_symmetric(sv_jk.mul(sv_im), sign_value::<T>(s_jk * s_im));
    T::axiom_eqv_transitive(sv_ij.mul(sv_mk), sign_value::<T>(s_ij * s_mk), sv_jk.mul(sv_im));

    // scale(sv_ij.mul(sv_mk), basis(m_mk)) ≡ scale(sv_jk.mul(sv_im), basis(m_im))
    lemma_scale_congruence_scalar(sv_ij.mul(sv_mk), sv_jk.mul(sv_im), basis::<T>(m_mk));

    // Final chain: LHS ≡ scale(sv_ij.mul(sv_mk), basis(m_mk)) ≡ scale(sv_jk.mul(sv_im), basis(m_im))
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(basis::<T>(i), basis::<T>(j)), basis::<T>(k)),
        scale(sv_ij.mul(sv_mk), basis(m_mk)),
        scale(sv_jk.mul(sv_im), basis(m_im)),
    );

    // scale(sv_jk.mul(sv_im), basis(m_im)) ≡ RHS [symmetric of RHS chain]
    Quat::<T>::axiom_eqv_symmetric(
        mul(basis::<T>(i), mul(basis::<T>(j), basis::<T>(k))),
        scale(sv_jk.mul(sv_im), basis(m_im)),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(basis::<T>(i), basis::<T>(j)), basis::<T>(k)),
        scale(sv_jk.mul(sv_im), basis(m_im)),
        mul(basis::<T>(i), mul(basis::<T>(j), basis::<T>(k))),
    );
}

} // verus!
