import Mathlib.Analysis.Complex.Trigonometric
import sympy.functions.elementary.hyperbolic
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  -- imply
  : Real.csch x = 1 / Real.sinh x := by
  -- proof
  rfl


-- created on 2023-11-26
