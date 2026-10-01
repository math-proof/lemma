import Mathlib.Analysis.SpecialFunctions.Sqrt
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x * x ≤ y * y) :
-- imply
  √(x * x) ≤ √(y * y) := by
-- proof
  exact Real.sqrt_le_sqrt h


-- created on 2026-09-27
