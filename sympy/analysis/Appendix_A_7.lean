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
abbrev make_twelve_equal_two : ℤ → ℤ → Prop := fun a b ↦ a = 12 ∧ b = 2

/-- A version of the integers where 12 has been forced to equal 2. -/
abbrev NewInt := Quot make_twelve_equal_two

/-- A coercion from integers to new integers -/
instance : Coe ℤ NewInt where
  coe n := Quot.mk make_twelve_equal_two n
theorem NewInt.is_coe (N:NewInt) : ∃ n:ℤ, N = (n:NewInt) := by
  apply Quot.ind (q := N); intro n
  use n

abbrev NewInt.quot {X:Type} {f: ℤ → X} (hf: f 12 = f 2) : NewInt → X := by
  apply Quot.lift f
  intro a b
  simp [make_twelve_equal_two]
  intro ha hb
  rw [ha, hb, hf]
