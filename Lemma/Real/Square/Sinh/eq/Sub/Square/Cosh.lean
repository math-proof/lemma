import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.sinh x ^ 2 = Real.cosh x ^ 2 - 1 := by
-- proof
  rw [Real.cosh_sq]
  ring


-- created on 2023-11-26
