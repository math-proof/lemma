import sympy.functions.elementary.trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : 0 < x) :
-- imply
  Real.sin x ≠ x := by
-- proof
  exact ne_of_lt (Real.sin_lt h)


-- created on 2023-10-03
