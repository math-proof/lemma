import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  -- given
  (hx : 0 ≤ x)
  -- imply
  : Real.arccos x = Real.arcsin (Real.sqrt (1 - x ^ 2)) := by
  -- proof
  exact Real.arccos_eq_arcsin hx

-- created on 2020-12-01
