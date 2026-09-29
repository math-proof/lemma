import Mathlib.Analysis.SpecialFunctions.Sqrt
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a : ℝ}
-- given
  (ha : a ≥ 0)
  (h₀ : x ≤ √a)
  (h₁ : -√a ≤ x) :
-- imply
  x ^ 2 ≤ a := by
-- proof
  calc x ^ 2 ≤ (√a) ^ 2 := sq_le_sq' h₁ h₀
    _ = a := Real.sq_sqrt ha


-- created on 2026-09-27
