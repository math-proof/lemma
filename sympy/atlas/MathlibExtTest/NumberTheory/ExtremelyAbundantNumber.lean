/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ExtremelyAbundantNumber.lean -/


import sympy.atlas.NumberTheory.ExtremelyAbundantNumber
import Mathlib.Tactic

namespace MetaMathlibExt

example : IsExtremelyAbundantNumber 10080 := by
  exact Or.inl rfl

example : ¬ IsExtremelyAbundantNumber 0 := by
  simp [IsExtremelyAbundantNumber]

example (n : Nat) (h : IsExtremelyAbundantNumber n) : n = 10080 ∨ 10080 < n := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr h.1

example (n m : Nat) (hn : 10080 < n) (h : IsExtremelyAbundantNumber n)
    (hm0 : 10080 ≤ m) (hmn : m < n) :
    ((ArithmeticFunction.sigma 1 n : Nat) : Real) /
        ((n : Real) * Real.log (Real.log (n : Real))) >
      ((ArithmeticFunction.sigma 1 m : Nat) : Real) /
        ((m : Real) * Real.log (Real.log (m : Real))) := by
  rcases h with h | h
  · omega
  · exact h.2 m hm0 hmn

#print axioms IsExtremelyAbundantNumber

end MetaMathlibExt
