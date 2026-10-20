import Mathlib.Tactic.LinearCombination
import sympy.Basic


@[path]
private lemma main
  {x y θ : ℝ} :
-- imply
  (x * Real.cos θ - y * Real.sin θ) ^ 2 + (x * Real.sin θ + y * Real.cos θ) ^ 2 = x ^ 2 + y ^ 2 := by
-- proof
  have h : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  linear_combination h * (x ^ 2 + y ^ 2)


-- created on 2023-06-09
-- updated on 2026-10-17
