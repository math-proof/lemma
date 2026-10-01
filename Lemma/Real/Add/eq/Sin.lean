import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  Real.sin x * Real.cos y + Real.sin y * Real.cos x = Real.sin (x + y) := by
-- proof
  rw [Real.sin_add]
  ring


-- created on 2023-06-01
