import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  (x y : ℝ) :
-- imply
  Real.cos x * Real.cos y + Real.sin x * Real.sin y = Real.cos (x - y) := by
-- proof
  rw [Real.cos_sub]


-- created on 2026-10-11
-- updated on 2026-10-17
