import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  Real.cosh x = Real.exp x / 2 + Real.exp (-x) / 2 := by
-- proof
  grind [Real.cosh_eq]


-- created on 2023-11-26
