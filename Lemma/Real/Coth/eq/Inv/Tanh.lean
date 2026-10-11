import Mathlib.Analysis.Complex.Trigonometric
import sympy.functions.elementary.hyperbolic
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  -- imply
  : Real.coth x = 1 / Real.tanh x := by
  -- proof
  rfl


-- created on 2023-11-26
