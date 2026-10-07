import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  -- imply
  : Real.tan x = Real.sin x / Real.cos x := by
  -- proof
  exact Real.tan_eq_sin_div_cos x


-- created on 2026-10-07
