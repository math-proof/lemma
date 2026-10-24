/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GiugaNumber.lean -/


import sympy.atlas.NumberTheory.GiugaNumber

namespace MetaMathlibExt


example (n : ℕ) : IsGiugaNumber n ↔
    2 ≤ n ∧ ¬ Nat.Prime n ∧ ∀ p, Nat.Prime p → p ∣ n → p ∣ (n / p - 1) := Iff.rfl

example : ¬ IsGiugaNumber 0 := by
  simp [IsGiugaNumber]

example : ¬ IsGiugaNumber 1 := by
  simp [IsGiugaNumber]

#print axioms IsGiugaNumber


end MetaMathlibExt
