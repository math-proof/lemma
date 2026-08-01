import sympy.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


@[main]
private lemma main
-- given
  (x y : ℝ) :
-- imply
  Real.cosh (x + y) = Real.sinh x * Real.sinh y + Real.cosh x * Real.cosh y := by
-- proof
  grind [Real.cosh_add]


-- created on 2023-11-26
