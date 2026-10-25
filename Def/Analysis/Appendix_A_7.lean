import Mathlib


/-!
# Analysis I, Appendix A.7: Equality

Introduction to equality in Lean

-/
def equality_as_equiv_relation (X:Type) : Setoid X := {
  r a b := a = b
  iseqv := {
    refl := Eq.refl
    symm := Eq.symm
    trans := Eq.trans
  }
}

