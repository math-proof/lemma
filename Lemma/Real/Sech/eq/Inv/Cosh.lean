import Mathlib.Analysis.Complex.Trigonometric
import sympy.functions.elementary.hyperbolic
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  -- imply
  : Real.sech x = 1 / Real.cosh x := by
  -- proof
  rfl


-- created on 2026-10-08
