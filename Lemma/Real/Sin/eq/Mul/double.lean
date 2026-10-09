import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ} :
-- imply
  Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
-- proof
  have h := Real.sin_two_mul (x / 2)
  ring_nf at h ⊢
  exact h


-- created on 2023-10-03
