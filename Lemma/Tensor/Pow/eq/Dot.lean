import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {h : Fin n → ℝ}
  {lam γ : ℝ}
-- given
  (h₀ : 0 ≤ lam)
  (h₁ : 0 ≤ γ) :
-- imply
  ∀ i, (lam * γ) ^ (h i) = lam ^ (h i) * γ ^ (h i) := by
-- proof
  intro i
  exact Real.mul_rpow h₀ h₁


-- created on 2023-04-16
-- updated on 2026-10-17
