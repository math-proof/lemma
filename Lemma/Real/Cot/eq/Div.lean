import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  -- imply
  : Real.cot x = Real.cos x / Real.sin x := by
  -- proof
  exact Real.cot_eq_cos_div_sin x

-- created on 2023-11-26
