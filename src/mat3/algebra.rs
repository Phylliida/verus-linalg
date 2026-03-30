use super::Mat3x3;
use crate::vec3::Vec3;
use verus_algebra::traits::*;
use vstd::prelude::*;

verus! {

impl<T: Ring> Equivalence for Mat3x3<T> {
    open spec fn eqv(self, other: Self) -> bool {
        self.row0.eqv(other.row0) && self.row1.eqv(other.row1) && self.row2.eqv(other.row2)
    }

    proof fn axiom_eqv_reflexive(a: Self) {
        Vec3::<T>::axiom_eqv_reflexive(a.row0);
        Vec3::<T>::axiom_eqv_reflexive(a.row1);
        Vec3::<T>::axiom_eqv_reflexive(a.row2);
    }

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {
        Vec3::<T>::axiom_eqv_symmetric(a.row0, b.row0);
        Vec3::<T>::axiom_eqv_symmetric(a.row1, b.row1);
        Vec3::<T>::axiom_eqv_symmetric(a.row2, b.row2);
    }

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        Vec3::<T>::axiom_eqv_transitive(a.row0, b.row0, c.row0);
        Vec3::<T>::axiom_eqv_transitive(a.row1, b.row1, c.row1);
        Vec3::<T>::axiom_eqv_transitive(a.row2, b.row2, c.row2);
    }

    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {
        if a == b {
            Vec3::<T>::axiom_eq_implies_eqv(a.row0, b.row0);
            Vec3::<T>::axiom_eq_implies_eqv(a.row1, b.row1);
            Vec3::<T>::axiom_eq_implies_eqv(a.row2, b.row2);
        }
    }
}

} //  verus!
