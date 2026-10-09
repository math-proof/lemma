import Mathlib.Analysis.Complex.Basic
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℂ}
-- given
  (h₀ : x ≠ 0)
  (h₁ : y ≠ 0) :
-- imply
  x / y ≠ 0 := by
-- proof
  exact div_ne_zero h₀ h₁


-- created on 2023-03-22
