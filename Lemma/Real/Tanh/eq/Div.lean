import Mathlib.Analysis.Complex.Trigonometric
import sympy.functions.elementary.hyperbolic
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  -- imply
  : Real.tanh x = Real.sinh x / Real.cosh x :=
  -- proof
  Real.tanh_eq_sinh_div_cosh x


-- created on 2026-10-08
