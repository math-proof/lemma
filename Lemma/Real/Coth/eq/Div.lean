import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.functions.elementary.hyperbolic
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.coth x = Real.cosh x / Real.sinh x := by
-- proof
  rw [Real.coth, Real.tanh_eq_sinh_div_cosh, one_div, inv_div]


-- created on 2023-11-26
-- updated on 2026-10-17
