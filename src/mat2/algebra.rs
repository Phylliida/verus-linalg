use vstd::prelude::*;
use verus_algebra::traits::*;
use crate::vec2::Vec2;
use super::Mat2x2;

verus! {

impl<T: Ring> Equivalence for Mat2x2<T> {
    open spec fn eqv(self, other: Self) -> bool {
        self.row0.eqv(other.row0) && self.row1.eqv(other.row1)
    }

    proof fn axiom_eqv_reflexive(a: Self) {
        Vec2::<T>::axiom_eqv_reflexive(a.row0);
        Vec2::<T>::axiom_eqv_reflexive(a.row1);
    }

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {
        Vec2::<T>::axiom_eqv_symmetric(a.row0, b.row0);
        Vec2::<T>::axiom_eqv_symmetric(a.row1, b.row1);
    }

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        Vec2::<T>::axiom_eqv_transitive(a.row0, b.row0, c.row0);
        Vec2::<T>::axiom_eqv_transitive(a.row1, b.row1, c.row1);
    }
}

impl<T: Ring> AdditiveCommutativeMonoid for Mat2x2<T> {
    open spec fn zero() -> Self {
        Mat2x2 { row0: Vec2::<T>::zero(), row1: Vec2::<T>::zero() }
    }

    open spec fn add(self, other: Self) -> Self {
        Mat2x2 {
            row0: self.row0.add(other.row0),
            row1: self.row1.add(other.row1),
        }
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {
        Vec2::<T>::axiom_add_commutative(a.row0, b.row0);
        Vec2::<T>::axiom_add_commutative(a.row1, b.row1);
    }

    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
        Vec2::<T>::axiom_add_associative(a.row0, b.row0, c.row0);
        Vec2::<T>::axiom_add_associative(a.row1, b.row1, c.row1);
    }

    proof fn axiom_add_zero_right(a: Self) {
        Vec2::<T>::axiom_add_zero_right(a.row0);
        Vec2::<T>::axiom_add_zero_right(a.row1);
    }

    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {
        Vec2::<T>::axiom_add_congruence_left(a.row0, b.row0, c.row0);
        Vec2::<T>::axiom_add_congruence_left(a.row1, b.row1, c.row1);
    }
}

impl<T: Ring> AdditiveGroup for Mat2x2<T> {
    open spec fn neg(self) -> Self {
        Mat2x2 {
            row0: self.row0.neg(),
            row1: self.row1.neg(),
        }
    }

    open spec fn sub(self, other: Self) -> Self {
        Mat2x2 {
            row0: self.row0.sub(other.row0),
            row1: self.row1.sub(other.row1),
        }
    }

    proof fn axiom_add_inverse_right(a: Self) {
        Vec2::<T>::axiom_add_inverse_right(a.row0);
        Vec2::<T>::axiom_add_inverse_right(a.row1);
    }

    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {
        Vec2::<T>::axiom_sub_is_add_neg(a.row0, b.row0);
        Vec2::<T>::axiom_sub_is_add_neg(a.row1, b.row1);
    }

    proof fn axiom_neg_congruence(a: Self, b: Self) {
        Vec2::<T>::axiom_neg_congruence(a.row0, b.row0);
        Vec2::<T>::axiom_neg_congruence(a.row1, b.row1);
    }
}

} // verus!
