use super::Mat4x4;
use crate::vec4::Vec4;
use verus_algebra::traits::*;
use vstd::prelude::*;

verus! {

impl<T: Ring> Equivalence for Mat4x4<T> {
    open spec fn eqv(self, other: Self) -> bool {
        self.row0.eqv(other.row0) && self.row1.eqv(other.row1)
        && self.row2.eqv(other.row2) && self.row3.eqv(other.row3)
    }

    proof fn axiom_eqv_reflexive(a: Self) {
        Vec4::<T>::axiom_eqv_reflexive(a.row0);
        Vec4::<T>::axiom_eqv_reflexive(a.row1);
        Vec4::<T>::axiom_eqv_reflexive(a.row2);
        Vec4::<T>::axiom_eqv_reflexive(a.row3);
    }

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {
        Vec4::<T>::axiom_eqv_symmetric(a.row0, b.row0);
        Vec4::<T>::axiom_eqv_symmetric(a.row1, b.row1);
        Vec4::<T>::axiom_eqv_symmetric(a.row2, b.row2);
        Vec4::<T>::axiom_eqv_symmetric(a.row3, b.row3);
    }

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        Vec4::<T>::axiom_eqv_transitive(a.row0, b.row0, c.row0);
        Vec4::<T>::axiom_eqv_transitive(a.row1, b.row1, c.row1);
        Vec4::<T>::axiom_eqv_transitive(a.row2, b.row2, c.row2);
        Vec4::<T>::axiom_eqv_transitive(a.row3, b.row3, c.row3);
    }

    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {
        if a == b {
            Vec4::<T>::axiom_eq_implies_eqv(a.row0, b.row0);
            Vec4::<T>::axiom_eq_implies_eqv(a.row1, b.row1);
            Vec4::<T>::axiom_eq_implies_eqv(a.row2, b.row2);
            Vec4::<T>::axiom_eq_implies_eqv(a.row3, b.row3);
        }
    }
}

} //  verus!
