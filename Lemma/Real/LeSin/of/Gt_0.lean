import sympy.functions.elementary.trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  Real.sin x ≤ x := by
-- proof
  exact le_of_lt (Real.sin_lt h)


-- created on 2023-10-03
