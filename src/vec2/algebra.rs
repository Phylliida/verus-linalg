use vstd::prelude::*;
use verus_algebra::traits::*;
use super::Vec2;

verus! {

impl<T: Ring> Equivalence for Vec2<T> {
    open spec fn eqv(self, other: Self) -> bool {
        self.x.eqv(other.x) && self.y.eqv(other.y)
    }

    proof fn axiom_eqv_reflexive(a: Self) {
        T::axiom_eqv_reflexive(a.x);
        T::axiom_eqv_reflexive(a.y);
    }

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {
        T::axiom_eqv_symmetric(a.x, b.x);
        T::axiom_eqv_symmetric(a.y, b.y);
    }

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        T::axiom_eqv_transitive(a.x, b.x, c.x);
        T::axiom_eqv_transitive(a.y, b.y, c.y);
    }
}

impl<T: Ring> AdditiveCommutativeMonoid for Vec2<T> {
    open spec fn zero() -> Self {
        Vec2 { x: T::zero(), y: T::zero() }
    }

    open spec fn add(self, other: Self) -> Self {
        Vec2 {
            x: self.x.add(other.x),
            y: self.y.add(other.y),
        }
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {
        T::axiom_add_commutative(a.x, b.x);
        T::axiom_add_commutative(a.y, b.y);
    }

    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
        T::axiom_add_associative(a.x, b.x, c.x);
        T::axiom_add_associative(a.y, b.y, c.y);
    }

    proof fn axiom_add_zero_right(a: Self) {
        T::axiom_add_zero_right(a.x);
        T::axiom_add_zero_right(a.y);
    }

    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {
        T::axiom_add_congruence_left(a.x, b.x, c.x);
        T::axiom_add_congruence_left(a.y, b.y, c.y);
    }
}

impl<T: Ring> AdditiveGroup for Vec2<T> {
    open spec fn neg(self) -> Self {
        Vec2 {
            x: self.x.neg(),
            y: self.y.neg(),
        }
    }

    open spec fn sub(self, other: Self) -> Self {
        Vec2 {
            x: self.x.sub(other.x),
            y: self.y.sub(other.y),
        }
    }

    proof fn axiom_add_inverse_right(a: Self) {
        T::axiom_add_inverse_right(a.x);
        T::axiom_add_inverse_right(a.y);
    }

    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {
        T::axiom_sub_is_add_neg(a.x, b.x);
        T::axiom_sub_is_add_neg(a.y, b.y);
    }

    proof fn axiom_neg_congruence(a: Self, b: Self) {
        T::axiom_neg_congruence(a.x, b.x);
        T::axiom_neg_congruence(a.y, b.y);
    }
}

} // verus!
