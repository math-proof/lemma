import Mathlib.Tactic
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h₀ : a ≠ 0) :
-- imply
  ∃ x : ℝ, a * x + b < 0 := by
-- proof
  refine ⟨(-b - 1) / a, ?_⟩
  have h₁ : a * ((-b - 1) / a) + b = -1 := by
    field_simp [h₀]
    ring
  linarith [h₁]


-- created on 2026-10-11
-- updated on 2026-10-17
