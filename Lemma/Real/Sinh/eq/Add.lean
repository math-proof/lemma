import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  Real.sinh (x + y) = Real.sinh x * Real.cosh y + Real.cosh x * Real.sinh y := by
-- proof
  exact Real.sinh_add x y


-- created on 2023-11-26
