import Mathlib.Analysis.SpecialFunctions.Sqrt
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a : ℝ}
-- given
  (h : x ^ 2 < a ^ 2) :
-- imply
  x ∈ Set.Ioo (-√(a ^ 2)) √(a ^ 2) := by
-- proof
  rw [← Real.sq_sqrt (sq_nonneg a)] at h
  apply Set.mem_Ioo.mpr (abs_lt_of_sq_lt_sq' h (Real.sqrt_nonneg _))


-- created on 2023-06-18
