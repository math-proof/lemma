import Mathlib.Analysis.SpecialFunctions.Sqrt
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h : x ^ 2 ≤ a) :
-- imply
  x ≤ √a ∧ -√a ≤ x := by
-- proof
  have := Real.abs_le_sqrt h
  exact ⟨(abs_le.mp this).2, (abs_le.mp this).1⟩


-- created on 2023-06-18
