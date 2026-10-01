import Mathlib.Analysis.SpecialFunctions.Sqrt
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (_h : x ≥ 0) :
-- imply
  √x ≥ 0 := by
-- proof
  exact Real.sqrt_nonneg x


-- created on 2026-09-27
