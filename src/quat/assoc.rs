use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::additive_group_lemmas;
use super::Quat;
use super::ops::*;
#[allow(unused_imports)]
use super::ops::mul;
use super::basis::*;

verus! {

// ===========================================================================
// Spec functions
// ===========================================================================

/// Associativity instance: (a*b)*c ≡ a*(b*c)
pub open spec fn assoc_instance<T: Ring>(a: Quat<T>, b: Quat<T>, c: Quat<T>) -> bool {
    mul(mul(a, b), c).eqv(mul(a, mul(b, c)))
}

/// Decompose quaternion as sum of scaled basis elements:
/// q = q.w*1 + q.x*i + q.y*j + q.z*k
pub open spec fn basis_decompose<T: Ring>(q: Quat<T>) -> Quat<T> {
    scale(q.w, basis(0)).add(scale(q.x, basis(1))).add(scale(q.y, basis(2))).add(scale(q.z, basis(3)))
}

// ===========================================================================
// Helpers: add congruence and simplification
// ===========================================================================

/// 4-way add congruence: a1+b1+c1+d1 ≡ a2+b2+c2+d2
proof fn lemma_aaa_cong<T: Ring>(a1: T, a2: T, b1: T, b2: T, c1: T, c2: T, d1: T, d2: T)
    requires a1.eqv(a2), b1.eqv(b2), c1.eqv(c2), d1.eqv(d2),
    ensures a1.add(b1).add(c1).add(d1).eqv(a2.add(b2).add(c2).add(d2)),
{
    additive_group_lemmas::lemma_add_congruence::<T>(a1, a2, b1, b2);
    additive_group_lemmas::lemma_add_congruence::<T>(a1.add(b1), a2.add(b2), c1, c2);
    additive_group_lemmas::lemma_add_congruence::<T>(a1.add(b1).add(c1), a2.add(b2).add(c2), d1, d2);
}

/// a + 0 + 0 + 0 ≡ a  (non-zero at position 0)
proof fn lemma_add_zeros_0<T: Ring>(a: T)
    ensures a.add(T::zero()).add(T::zero()).add(T::zero()).eqv(a),
{
    let z = T::zero();
    T::axiom_add_zero_right(a);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_add_congruence::<T>(a.add(z), a, z, z);
    T::axiom_eqv_transitive(a.add(z).add(z), a.add(z), a);
    additive_group_lemmas::lemma_add_congruence::<T>(a.add(z).add(z), a, z, z);
    T::axiom_eqv_transitive(a.add(z).add(z).add(z), a.add(z), a);
}

/// 0 + a + 0 + 0 ≡ a  (non-zero at position 1)
proof fn lemma_add_zeros_1<T: Ring>(a: T)
    ensures T::zero().add(a).add(T::zero()).add(T::zero()).eqv(a),
{
    let z = T::zero();
    additive_group_lemmas::lemma_add_zero_left::<T>(a);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_add_congruence::<T>(z.add(a), a, z, z);
    T::axiom_add_zero_right(a);
    T::axiom_eqv_transitive(z.add(a).add(z), a.add(z), a);
    additive_group_lemmas::lemma_add_congruence::<T>(z.add(a).add(z), a, z, z);
    T::axiom_eqv_transitive(z.add(a).add(z).add(z), a.add(z), a);
}

/// 0 + 0 + a + 0 ≡ a  (non-zero at position 2)
proof fn lemma_add_zeros_2<T: Ring>(a: T)
    ensures T::zero().add(T::zero()).add(a).add(T::zero()).eqv(a),
{
    let z = T::zero();
    T::axiom_add_zero_right(z);
    T::axiom_eqv_reflexive(a);
    additive_group_lemmas::lemma_add_congruence::<T>(z.add(z), z, a, a);
    additive_group_lemmas::lemma_add_zero_left::<T>(a);
    T::axiom_eqv_transitive(z.add(z).add(a), z.add(a), a);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_add_congruence::<T>(z.add(z).add(a), a, z, z);
    T::axiom_add_zero_right(a);
    T::axiom_eqv_transitive(z.add(z).add(a).add(z), a.add(z), a);
}

/// 0 + 0 + 0 + a ≡ a  (non-zero at position 3)
proof fn lemma_add_zeros_3<T: Ring>(a: T)
    ensures T::zero().add(T::zero()).add(T::zero()).add(a).eqv(a),
{
    let z = T::zero();
    T::axiom_add_zero_right(z);
    T::axiom_eqv_reflexive(z);
    additive_group_lemmas::lemma_add_congruence::<T>(z.add(z), z, z, z);
    T::axiom_eqv_transitive(z.add(z).add(z), z.add(z), z);
    T::axiom_eqv_reflexive(a);
    additive_group_lemmas::lemma_add_congruence::<T>(z.add(z).add(z), z, a, a);
    additive_group_lemmas::lemma_add_zero_left::<T>(a);
    T::axiom_eqv_transitive(z.add(z).add(z).add(a), z.add(a), a);
}

// ===========================================================================
// Basis decomposition equivalence
// ===========================================================================

/// Every quaternion is eqv to its basis decomposition
pub proof fn lemma_basis_decompose_eqv<T: Ring>(q: Quat<T>)
    ensures q.eqv(basis_decompose(q)),
{
    let z = T::zero(); let o = T::one();
    // Establish product facts: q.c * 1 ≡ q.c, q.c * 0 ≡ 0
    T::axiom_mul_one_right(q.w); T::axiom_mul_zero_right(q.w);
    T::axiom_mul_one_right(q.x); T::axiom_mul_zero_right(q.x);
    T::axiom_mul_one_right(q.y); T::axiom_mul_zero_right(q.y);
    T::axiom_mul_one_right(q.z); T::axiom_mul_zero_right(q.z);

    // w-component: q.w*1 + q.x*0 + q.y*0 + q.z*0 ≡ q.w + 0 + 0 + 0 ≡ q.w
    lemma_aaa_cong::<T>(q.w.mul(o), q.w, q.x.mul(z), z, q.y.mul(z), z, q.z.mul(z), z);
    lemma_add_zeros_0::<T>(q.w);
    T::axiom_eqv_transitive(basis_decompose(q).w, q.w.add(z).add(z).add(z), q.w);
    T::axiom_eqv_symmetric(q.w, basis_decompose(q).w);

    // x-component: q.w*0 + q.x*1 + q.y*0 + q.z*0 ≡ 0 + q.x + 0 + 0 ≡ q.x
    lemma_aaa_cong::<T>(q.w.mul(z), z, q.x.mul(o), q.x, q.y.mul(z), z, q.z.mul(z), z);
    lemma_add_zeros_1::<T>(q.x);
    T::axiom_eqv_transitive(basis_decompose(q).x, z.add(q.x).add(z).add(z), q.x);
    T::axiom_eqv_symmetric(q.x, basis_decompose(q).x);

    // y-component: q.w*0 + q.x*0 + q.y*1 + q.z*0 ≡ 0 + 0 + q.y + 0 ≡ q.y
    lemma_aaa_cong::<T>(q.w.mul(z), z, q.x.mul(z), z, q.y.mul(o), q.y, q.z.mul(z), z);
    lemma_add_zeros_2::<T>(q.y);
    T::axiom_eqv_transitive(basis_decompose(q).y, z.add(z).add(q.y).add(z), q.y);
    T::axiom_eqv_symmetric(q.y, basis_decompose(q).y);

    // z-component: q.w*0 + q.x*0 + q.y*0 + q.z*1 ≡ 0 + 0 + 0 + q.z ≡ q.z
    lemma_aaa_cong::<T>(q.w.mul(z), z, q.x.mul(z), z, q.y.mul(z), z, q.z.mul(o), q.z);
    lemma_add_zeros_3::<T>(q.z);
    T::axiom_eqv_transitive(basis_decompose(q).z, z.add(z).add(z).add(q.z), q.z);
    T::axiom_eqv_symmetric(q.z, basis_decompose(q).z);
}

// ===========================================================================
// Linearity lemmas: right position
// ===========================================================================

/// If assoc(a,b,c1) and assoc(a,b,c2), then assoc(a,b,c1+c2)
proof fn lemma_assoc_linear_right_add<T: Ring>(a: Quat<T>, b: Quat<T>, c1: Quat<T>, c2: Quat<T>)
    requires assoc_instance(a, b, c1), assoc_instance(a, b, c2),
    ensures assoc_instance(a, b, c1.add(c2)),
{
    let ab = mul(a, b);
    // LHS: mul(ab, c1+c2) ≡ mul(ab,c1) + mul(ab,c2)
    lemma_mul_distributes_right(ab, c1, c2);
    // ≡ mul(a,mul(b,c1)) + mul(a,mul(b,c2))  [premises via add_congruence]
    additive_group_lemmas::lemma_add_congruence::<Quat<T>>(
        mul(ab, c1), mul(a, mul(b, c1)),
        mul(ab, c2), mul(a, mul(b, c2)),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(ab, c1.add(c2)),
        mul(ab, c1).add(mul(ab, c2)),
        mul(a, mul(b, c1)).add(mul(a, mul(b, c2))),
    );
    // RHS: mul(a, mul(b, c1+c2))
    lemma_mul_distributes_right(b, c1, c2);
    lemma_mul_congruence_right(a, mul(b, c1.add(c2)), mul(b, c1).add(mul(b, c2)));
    lemma_mul_distributes_right(a, mul(b, c1), mul(b, c2));
    Quat::<T>::axiom_eqv_transitive(
        mul(a, mul(b, c1.add(c2))),
        mul(a, mul(b, c1).add(mul(b, c2))),
        mul(a, mul(b, c1)).add(mul(a, mul(b, c2))),
    );
    // Connect
    Quat::<T>::axiom_eqv_symmetric(
        mul(a, mul(b, c1.add(c2))),
        mul(a, mul(b, c1)).add(mul(a, mul(b, c2))),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(ab, c1.add(c2)),
        mul(a, mul(b, c1)).add(mul(a, mul(b, c2))),
        mul(a, mul(b, c1.add(c2))),
    );
}

/// If assoc(a,b,c), then assoc(a,b,scale(k,c))
proof fn lemma_assoc_linear_right_scale<T: Ring>(a: Quat<T>, b: Quat<T>, c: Quat<T>, k: T)
    requires assoc_instance(a, b, c),
    ensures assoc_instance(a, b, scale(k, c)),
{
    let ab = mul(a, b);
    // LHS: mul(ab, scale(k,c)) ≡ scale(k, mul(ab,c)) ≡ scale(k, mul(a,mul(b,c)))
    lemma_mul_scale_right(ab, k, c);
    lemma_scale_congruence(k, mul(ab, c), mul(a, mul(b, c)));
    Quat::<T>::axiom_eqv_transitive(
        mul(ab, scale(k, c)), scale(k, mul(ab, c)), scale(k, mul(a, mul(b, c))),
    );
    // RHS: mul(a, mul(b, scale(k,c))) ≡ mul(a, scale(k, mul(b,c))) ≡ scale(k, mul(a,mul(b,c)))
    lemma_mul_scale_right(b, k, c);
    lemma_mul_congruence_right(a, mul(b, scale(k, c)), scale(k, mul(b, c)));
    lemma_mul_scale_right(a, k, mul(b, c));
    Quat::<T>::axiom_eqv_transitive(
        mul(a, mul(b, scale(k, c))),
        mul(a, scale(k, mul(b, c))),
        scale(k, mul(a, mul(b, c))),
    );
    // Connect
    Quat::<T>::axiom_eqv_symmetric(
        mul(a, mul(b, scale(k, c))),
        scale(k, mul(a, mul(b, c))),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(ab, scale(k, c)),
        scale(k, mul(a, mul(b, c))),
        mul(a, mul(b, scale(k, c))),
    );
}

// ===========================================================================
// Linearity lemmas: middle position
// ===========================================================================

/// If assoc(a,b1,c) and assoc(a,b2,c), then assoc(a,b1+b2,c)
proof fn lemma_assoc_linear_middle_add<T: Ring>(a: Quat<T>, b1: Quat<T>, b2: Quat<T>, c: Quat<T>)
    requires assoc_instance(a, b1, c), assoc_instance(a, b2, c),
    ensures assoc_instance(a, b1.add(b2), c),
{
    // LHS: mul(mul(a, b1+b2), c)
    lemma_mul_distributes_right(a, b1, b2);
    lemma_mul_congruence_left(mul(a, b1.add(b2)), mul(a, b1).add(mul(a, b2)), c);
    lemma_mul_distributes_left(mul(a, b1), mul(a, b2), c);
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(a, b1.add(b2)), c),
        mul(mul(a, b1).add(mul(a, b2)), c),
        mul(mul(a, b1), c).add(mul(mul(a, b2), c)),
    );
    // ≡ mul(a,mul(b1,c)) + mul(a,mul(b2,c))
    additive_group_lemmas::lemma_add_congruence::<Quat<T>>(
        mul(mul(a, b1), c), mul(a, mul(b1, c)),
        mul(mul(a, b2), c), mul(a, mul(b2, c)),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(a, b1.add(b2)), c),
        mul(mul(a, b1), c).add(mul(mul(a, b2), c)),
        mul(a, mul(b1, c)).add(mul(a, mul(b2, c))),
    );
    // RHS: mul(a, mul(b1+b2, c))
    lemma_mul_distributes_left(b1, b2, c);
    lemma_mul_congruence_right(a, mul(b1.add(b2), c), mul(b1, c).add(mul(b2, c)));
    lemma_mul_distributes_right(a, mul(b1, c), mul(b2, c));
    Quat::<T>::axiom_eqv_transitive(
        mul(a, mul(b1.add(b2), c)),
        mul(a, mul(b1, c).add(mul(b2, c))),
        mul(a, mul(b1, c)).add(mul(a, mul(b2, c))),
    );
    // Connect
    Quat::<T>::axiom_eqv_symmetric(
        mul(a, mul(b1.add(b2), c)),
        mul(a, mul(b1, c)).add(mul(a, mul(b2, c))),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(a, b1.add(b2)), c),
        mul(a, mul(b1, c)).add(mul(a, mul(b2, c))),
        mul(a, mul(b1.add(b2), c)),
    );
}

/// If assoc(a,b,c), then assoc(a,scale(k,b),c)
proof fn lemma_assoc_linear_middle_scale<T: Ring>(a: Quat<T>, b: Quat<T>, c: Quat<T>, k: T)
    requires assoc_instance(a, b, c),
    ensures assoc_instance(a, scale(k, b), c),
{
    // LHS: mul(mul(a, scale(k,b)), c)
    lemma_mul_scale_right(a, k, b);
    lemma_mul_congruence_left(mul(a, scale(k, b)), scale(k, mul(a, b)), c);
    lemma_mul_scale_left(k, mul(a, b), c);
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(a, scale(k, b)), c),
        mul(scale(k, mul(a, b)), c),
        scale(k, mul(mul(a, b), c)),
    );
    lemma_scale_congruence(k, mul(mul(a, b), c), mul(a, mul(b, c)));
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(a, scale(k, b)), c),
        scale(k, mul(mul(a, b), c)),
        scale(k, mul(a, mul(b, c))),
    );
    // RHS: mul(a, mul(scale(k,b), c))
    lemma_mul_scale_left(k, b, c);
    lemma_mul_congruence_right(a, mul(scale(k, b), c), scale(k, mul(b, c)));
    lemma_mul_scale_right(a, k, mul(b, c));
    Quat::<T>::axiom_eqv_transitive(
        mul(a, mul(scale(k, b), c)),
        mul(a, scale(k, mul(b, c))),
        scale(k, mul(a, mul(b, c))),
    );
    // Connect
    Quat::<T>::axiom_eqv_symmetric(
        mul(a, mul(scale(k, b), c)),
        scale(k, mul(a, mul(b, c))),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(a, scale(k, b)), c),
        scale(k, mul(a, mul(b, c))),
        mul(a, mul(scale(k, b), c)),
    );
}

// ===========================================================================
// Linearity lemmas: left position
// ===========================================================================

/// If assoc(a1,b,c) and assoc(a2,b,c), then assoc(a1+a2,b,c)
proof fn lemma_assoc_linear_left_add<T: Ring>(a1: Quat<T>, a2: Quat<T>, b: Quat<T>, c: Quat<T>)
    requires assoc_instance(a1, b, c), assoc_instance(a2, b, c),
    ensures assoc_instance(a1.add(a2), b, c),
{
    let bc = mul(b, c);
    // LHS: mul(mul(a1+a2, b), c)
    lemma_mul_distributes_left(a1, a2, b);
    lemma_mul_congruence_left(mul(a1.add(a2), b), mul(a1, b).add(mul(a2, b)), c);
    lemma_mul_distributes_left(mul(a1, b), mul(a2, b), c);
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(a1.add(a2), b), c),
        mul(mul(a1, b).add(mul(a2, b)), c),
        mul(mul(a1, b), c).add(mul(mul(a2, b), c)),
    );
    additive_group_lemmas::lemma_add_congruence::<Quat<T>>(
        mul(mul(a1, b), c), mul(a1, bc),
        mul(mul(a2, b), c), mul(a2, bc),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(a1.add(a2), b), c),
        mul(mul(a1, b), c).add(mul(mul(a2, b), c)),
        mul(a1, bc).add(mul(a2, bc)),
    );
    // RHS: mul(a1+a2, bc) ≡ mul(a1,bc) + mul(a2,bc)
    lemma_mul_distributes_left(a1, a2, bc);
    // Connect
    Quat::<T>::axiom_eqv_symmetric(
        mul(a1.add(a2), bc),
        mul(a1, bc).add(mul(a2, bc)),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(a1.add(a2), b), c),
        mul(a1, bc).add(mul(a2, bc)),
        mul(a1.add(a2), bc),
    );
}

/// If assoc(a,b,c), then assoc(scale(k,a),b,c)
proof fn lemma_assoc_linear_left_scale<T: Ring>(a: Quat<T>, b: Quat<T>, c: Quat<T>, k: T)
    requires assoc_instance(a, b, c),
    ensures assoc_instance(scale(k, a), b, c),
{
    // LHS: mul(mul(scale(k,a), b), c)
    lemma_mul_scale_left(k, a, b);
    lemma_mul_congruence_left(mul(scale(k, a), b), scale(k, mul(a, b)), c);
    lemma_mul_scale_left(k, mul(a, b), c);
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(scale(k, a), b), c),
        mul(scale(k, mul(a, b)), c),
        scale(k, mul(mul(a, b), c)),
    );
    lemma_scale_congruence(k, mul(mul(a, b), c), mul(a, mul(b, c)));
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(scale(k, a), b), c),
        scale(k, mul(mul(a, b), c)),
        scale(k, mul(a, mul(b, c))),
    );
    // RHS: mul(scale(k,a), mul(b,c)) ≡ scale(k, mul(a, mul(b,c)))
    lemma_mul_scale_left(k, a, mul(b, c));
    // Connect
    Quat::<T>::axiom_eqv_symmetric(
        mul(scale(k, a), mul(b, c)),
        scale(k, mul(a, mul(b, c))),
    );
    Quat::<T>::axiom_eqv_transitive(
        mul(mul(scale(k, a), b), c),
        scale(k, mul(a, mul(b, c))),
        mul(scale(k, a), mul(b, c)),
    );
}

// ===========================================================================
// Equivalence transfer lemmas
// ===========================================================================

/// Transfer assoc through eqv on right: assoc(a,b,c1) ∧ c1≡c2 → assoc(a,b,c2)
proof fn lemma_assoc_eqv_right<T: Ring>(a: Quat<T>, b: Quat<T>, c1: Quat<T>, c2: Quat<T>)
    requires assoc_instance(a, b, c1), c1.eqv(c2),
    ensures assoc_instance(a, b, c2),
{
    let ab = mul(a, b);
    // mul(ab, c1) ≡ mul(ab, c2) via congruence
    lemma_mul_congruence_right(ab, c1, c2);
    Quat::<T>::axiom_eqv_symmetric(mul(ab, c1), mul(ab, c2));
    Quat::<T>::axiom_eqv_transitive(mul(ab, c2), mul(ab, c1), mul(a, mul(b, c1)));
    // mul(a, mul(b, c1)) ≡ mul(a, mul(b, c2)) via congruence
    lemma_mul_congruence_right(b, c1, c2);
    lemma_mul_congruence_right(a, mul(b, c1), mul(b, c2));
    Quat::<T>::axiom_eqv_transitive(mul(ab, c2), mul(a, mul(b, c1)), mul(a, mul(b, c2)));
}

/// Transfer assoc through eqv on middle: assoc(a,b1,c) ∧ b1≡b2 → assoc(a,b2,c)
proof fn lemma_assoc_eqv_middle<T: Ring>(a: Quat<T>, b1: Quat<T>, b2: Quat<T>, c: Quat<T>)
    requires assoc_instance(a, b1, c), b1.eqv(b2),
    ensures assoc_instance(a, b2, c),
{
    lemma_mul_congruence_right(a, b1, b2);
    lemma_mul_congruence_left(mul(a, b1), mul(a, b2), c);
    Quat::<T>::axiom_eqv_symmetric(mul(mul(a, b1), c), mul(mul(a, b2), c));
    Quat::<T>::axiom_eqv_transitive(mul(mul(a, b2), c), mul(mul(a, b1), c), mul(a, mul(b1, c)));
    lemma_mul_congruence_left(b1, b2, c);
    lemma_mul_congruence_right(a, mul(b1, c), mul(b2, c));
    Quat::<T>::axiom_eqv_transitive(mul(mul(a, b2), c), mul(a, mul(b1, c)), mul(a, mul(b2, c)));
}

/// Transfer assoc through eqv on left: assoc(a1,b,c) ∧ a1≡a2 → assoc(a2,b,c)
proof fn lemma_assoc_eqv_left<T: Ring>(a1: Quat<T>, a2: Quat<T>, b: Quat<T>, c: Quat<T>)
    requires assoc_instance(a1, b, c), a1.eqv(a2),
    ensures assoc_instance(a2, b, c),
{
    let bc = mul(b, c);
    lemma_mul_congruence_left(a1, a2, b);
    lemma_mul_congruence_left(mul(a1, b), mul(a2, b), c);
    Quat::<T>::axiom_eqv_symmetric(mul(mul(a1, b), c), mul(mul(a2, b), c));
    Quat::<T>::axiom_eqv_transitive(mul(mul(a2, b), c), mul(mul(a1, b), c), mul(a1, bc));
    lemma_mul_congruence_left(a1, a2, bc);
    Quat::<T>::axiom_eqv_transitive(mul(mul(a2, b), c), mul(a1, bc), mul(a2, bc));
}

// ===========================================================================
// Linearization fold helpers
// ===========================================================================

/// Given assoc for all 4 basis elements as c, derive assoc for arbitrary c
proof fn lemma_linearize_right<T: Ring>(a: Quat<T>, b: Quat<T>, c: Quat<T>)
    requires
        assoc_instance(a, b, basis(0)),
        assoc_instance(a, b, basis(1)),
        assoc_instance(a, b, basis(2)),
        assoc_instance(a, b, basis(3)),
    ensures assoc_instance(a, b, c),
{
    lemma_assoc_linear_right_scale(a, b, basis(0), c.w);
    lemma_assoc_linear_right_scale(a, b, basis(1), c.x);
    lemma_assoc_linear_right_scale(a, b, basis(2), c.y);
    lemma_assoc_linear_right_scale(a, b, basis(3), c.z);
    lemma_assoc_linear_right_add(a, b, scale(c.w, basis(0)), scale(c.x, basis(1)));
    lemma_assoc_linear_right_add(a, b,
        scale(c.w, basis(0)).add(scale(c.x, basis(1))), scale(c.y, basis(2)));
    lemma_assoc_linear_right_add(a, b,
        scale(c.w, basis(0)).add(scale(c.x, basis(1))).add(scale(c.y, basis(2))),
        scale(c.z, basis(3)));
    // Now have assoc(a, b, basis_decompose(c))
    lemma_basis_decompose_eqv(c);
    Quat::<T>::axiom_eqv_symmetric(c, basis_decompose(c));
    lemma_assoc_eqv_right(a, b, basis_decompose(c), c);
}

/// Given assoc for all 4 basis elements as b, derive assoc for arbitrary b
proof fn lemma_linearize_middle<T: Ring>(a: Quat<T>, b: Quat<T>, c: Quat<T>)
    requires
        assoc_instance(a, basis(0), c),
        assoc_instance(a, basis(1), c),
        assoc_instance(a, basis(2), c),
        assoc_instance(a, basis(3), c),
    ensures assoc_instance(a, b, c),
{
    lemma_assoc_linear_middle_scale(a, basis(0), c, b.w);
    lemma_assoc_linear_middle_scale(a, basis(1), c, b.x);
    lemma_assoc_linear_middle_scale(a, basis(2), c, b.y);
    lemma_assoc_linear_middle_scale(a, basis(3), c, b.z);
    lemma_assoc_linear_middle_add(a, scale(b.w, basis(0)), scale(b.x, basis(1)), c);
    lemma_assoc_linear_middle_add(a,
        scale(b.w, basis(0)).add(scale(b.x, basis(1))), scale(b.y, basis(2)), c);
    lemma_assoc_linear_middle_add(a,
        scale(b.w, basis(0)).add(scale(b.x, basis(1))).add(scale(b.y, basis(2))),
        scale(b.z, basis(3)), c);
    lemma_basis_decompose_eqv(b);
    Quat::<T>::axiom_eqv_symmetric(b, basis_decompose(b));
    lemma_assoc_eqv_middle(a, basis_decompose(b), b, c);
}

/// Given assoc for all 4 basis elements as a, derive assoc for arbitrary a
proof fn lemma_linearize_left<T: Ring>(a: Quat<T>, b: Quat<T>, c: Quat<T>)
    requires
        assoc_instance(basis(0), b, c),
        assoc_instance(basis(1), b, c),
        assoc_instance(basis(2), b, c),
        assoc_instance(basis(3), b, c),
    ensures assoc_instance(a, b, c),
{
    lemma_assoc_linear_left_scale(basis(0), b, c, a.w);
    lemma_assoc_linear_left_scale(basis(1), b, c, a.x);
    lemma_assoc_linear_left_scale(basis(2), b, c, a.y);
    lemma_assoc_linear_left_scale(basis(3), b, c, a.z);
    lemma_assoc_linear_left_add(scale(a.w, basis(0)), scale(a.x, basis(1)), b, c);
    lemma_assoc_linear_left_add(
        scale(a.w, basis(0)).add(scale(a.x, basis(1))), scale(a.y, basis(2)), b, c);
    lemma_assoc_linear_left_add(
        scale(a.w, basis(0)).add(scale(a.x, basis(1))).add(scale(a.y, basis(2))),
        scale(a.z, basis(3)), b, c);
    lemma_basis_decompose_eqv(a);
    Quat::<T>::axiom_eqv_symmetric(a, basis_decompose(a));
    lemma_assoc_eqv_left(basis_decompose(a), a, b, c);
}

// ===========================================================================
// Assembly: basis element with arbitrary b, c
// ===========================================================================

/// assoc(basis(i), b, c) for arbitrary b, c
proof fn lemma_assoc_basis_any<T: Ring>(i: int, b: Quat<T>, c: Quat<T>)
    requires 0 <= i < 4,
    ensures assoc_instance(basis::<T>(i), b, c),
{
    // For each j, establish assoc(basis(i), basis(j), basis(k)) for all k, then linearize c
    lemma_basis_assoc_indices::<T>(i, 0, 0);
    lemma_basis_assoc_indices::<T>(i, 0, 1);
    lemma_basis_assoc_indices::<T>(i, 0, 2);
    lemma_basis_assoc_indices::<T>(i, 0, 3);
    lemma_linearize_right(basis(i), basis(0), c);

    lemma_basis_assoc_indices::<T>(i, 1, 0);
    lemma_basis_assoc_indices::<T>(i, 1, 1);
    lemma_basis_assoc_indices::<T>(i, 1, 2);
    lemma_basis_assoc_indices::<T>(i, 1, 3);
    lemma_linearize_right(basis(i), basis(1), c);

    lemma_basis_assoc_indices::<T>(i, 2, 0);
    lemma_basis_assoc_indices::<T>(i, 2, 1);
    lemma_basis_assoc_indices::<T>(i, 2, 2);
    lemma_basis_assoc_indices::<T>(i, 2, 3);
    lemma_linearize_right(basis(i), basis(2), c);

    lemma_basis_assoc_indices::<T>(i, 3, 0);
    lemma_basis_assoc_indices::<T>(i, 3, 1);
    lemma_basis_assoc_indices::<T>(i, 3, 2);
    lemma_basis_assoc_indices::<T>(i, 3, 3);
    lemma_linearize_right(basis(i), basis(3), c);

    // Now have assoc(basis(i), basis(j), c) for all j. Linearize b.
    lemma_linearize_middle(basis(i), b, c);
}

// ===========================================================================
// Top-level: quaternion multiplication is associative
// ===========================================================================

/// (a*b)*c ≡ a*(b*c) for all quaternions
pub proof fn lemma_mul_associative<T: Ring>(a: Quat<T>, b: Quat<T>, c: Quat<T>)
    ensures mul(mul(a, b), c).eqv(mul(a, mul(b, c))),
{
    lemma_assoc_basis_any::<T>(0, b, c);
    lemma_assoc_basis_any::<T>(1, b, c);
    lemma_assoc_basis_any::<T>(2, b, c);
    lemma_assoc_basis_any::<T>(3, b, c);
    lemma_linearize_left(a, b, c);
}

} // verus!
