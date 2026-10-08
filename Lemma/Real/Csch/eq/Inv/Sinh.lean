import Mathlib.Analysis.Complex.Trigonometric
import sympy.functions.elementary.hyperbolic
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  -- imply
  : Real.csch x = 1 / Real.sinh x := by
  -- proof
  rfl


-- created on 2026-10-08
