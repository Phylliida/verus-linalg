use super::Quat;
use verus_algebra::traits::*;
use vstd::prelude::*;

verus! {

impl<T: Ring> Equivalence for Quat<T> {
    open spec fn eqv(self, other: Self) -> bool {
        self.w.eqv(other.w) && self.x.eqv(other.x)
            && self.y.eqv(other.y) && self.z.eqv(other.z)
    }

    proof fn axiom_eqv_reflexive(a: Self) {
        T::axiom_eqv_reflexive(a.w);
        T::axiom_eqv_reflexive(a.x);
        T::axiom_eqv_reflexive(a.y);
        T::axiom_eqv_reflexive(a.z);
    }

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {
        T::axiom_eqv_symmetric(a.w, b.w);
        T::axiom_eqv_symmetric(a.x, b.x);
        T::axiom_eqv_symmetric(a.y, b.y);
        T::axiom_eqv_symmetric(a.z, b.z);
    }

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        T::axiom_eqv_transitive(a.w, b.w, c.w);
        T::axiom_eqv_transitive(a.x, b.x, c.x);
        T::axiom_eqv_transitive(a.y, b.y, c.y);
        T::axiom_eqv_transitive(a.z, b.z, c.z);
    }

    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {
        if a == b {
            T::axiom_eq_implies_eqv(a.w, b.w);
            T::axiom_eq_implies_eqv(a.x, b.x);
            T::axiom_eq_implies_eqv(a.y, b.y);
            T::axiom_eq_implies_eqv(a.z, b.z);
        }
    }
}

impl<T: Ring> AdditiveCommutativeMonoid for Quat<T> {
    open spec fn zero() -> Self {
        Quat { w: T::zero(), x: T::zero(), y: T::zero(), z: T::zero() }
    }

    open spec fn add(self, other: Self) -> Self {
        Quat {
            w: self.w.add(other.w),
            x: self.x.add(other.x),
            y: self.y.add(other.y),
            z: self.z.add(other.z),
        }
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {
        T::axiom_add_commutative(a.w, b.w);
        T::axiom_add_commutative(a.x, b.x);
        T::axiom_add_commutative(a.y, b.y);
        T::axiom_add_commutative(a.z, b.z);
    }

    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
        T::axiom_add_associative(a.w, b.w, c.w);
        T::axiom_add_associative(a.x, b.x, c.x);
        T::axiom_add_associative(a.y, b.y, c.y);
        T::axiom_add_associative(a.z, b.z, c.z);
    }

    proof fn axiom_add_zero_right(a: Self) {
        T::axiom_add_zero_right(a.w);
        T::axiom_add_zero_right(a.x);
        T::axiom_add_zero_right(a.y);
        T::axiom_add_zero_right(a.z);
    }

    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {
        T::axiom_add_congruence_left(a.w, b.w, c.w);
        T::axiom_add_congruence_left(a.x, b.x, c.x);
        T::axiom_add_congruence_left(a.y, b.y, c.y);
        T::axiom_add_congruence_left(a.z, b.z, c.z);
    }
}

impl<T: Ring> AdditiveGroup for Quat<T> {
    open spec fn neg(self) -> Self {
        Quat {
            w: self.w.neg(),
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
        }
    }

    open spec fn sub(self, other: Self) -> Self {
        Quat {
            w: self.w.sub(other.w),
            x: self.x.sub(other.x),
            y: self.y.sub(other.y),
            z: self.z.sub(other.z),
        }
    }

    proof fn axiom_add_inverse_right(a: Self) {
        T::axiom_add_inverse_right(a.w);
        T::axiom_add_inverse_right(a.x);
        T::axiom_add_inverse_right(a.y);
        T::axiom_add_inverse_right(a.z);
    }

    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {
        T::axiom_sub_is_add_neg(a.w, b.w);
        T::axiom_sub_is_add_neg(a.x, b.x);
        T::axiom_sub_is_add_neg(a.y, b.y);
        T::axiom_sub_is_add_neg(a.z, b.z);
    }

    proof fn axiom_neg_congruence(a: Self, b: Self) {
        T::axiom_neg_congruence(a.w, b.w);
        T::axiom_neg_congruence(a.x, b.x);
        T::axiom_neg_congruence(a.y, b.y);
        T::axiom_neg_congruence(a.z, b.z);
    }
}

} // verus!
