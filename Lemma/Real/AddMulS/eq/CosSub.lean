import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
  -- imply
  : Real.cos x * Real.cos y + Real.sin x * Real.sin y = Real.cos (x - y) := by
  -- proof
  exact (Real.cos_sub x y).symm

-- created on 2019-11-26
