import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[main]
private lemma main
-- given
  (x y : ℝ) :
-- imply
  Real.sinh (x - y) = -Real.sinh (y - x) := by
-- proof
  have h := Real.sinh_neg (x - y)
  rw [show -(x - y) = y - x by ring] at h
  linarith


-- created on 2023-11-26
