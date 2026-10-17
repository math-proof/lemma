import Mathlib.Analysis.Calculus.Deriv.Basic
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {a b x₀ x₁ : ℝ}
-- given
  (h₀ : ∀ x ∈ Set.Ioo a b, 0 < deriv (deriv f) x)
  (h₁ : x₀ ∈ Set.Ioo a b)
  (h₂ : x₁ ∈ Set.Ioo a b) :
-- imply
  DifferentiableAt ℝ (deriv f) x₀ ∧ DifferentiableAt ℝ (deriv f) x₁ :=
-- proof
  ⟨differentiableAt_of_deriv_ne_zero (h₀ x₀ h₁).ne',
    differentiableAt_of_deriv_ne_zero (h₀ x₁ h₂).ne'⟩


-- created on 2026-10-11
-- updated on 2026-10-17
