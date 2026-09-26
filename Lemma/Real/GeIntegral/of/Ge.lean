import sympy.integrals.integrals
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (h₀ : a ≤ b)
  (h₁ : f ∈ ℒ¹ a b)
  (h₂ : g ∈ ℒ¹ a b)
  (h₃ : f ≥ g) :
-- imply
  ∫ x : ℝ in a..b, f x ≥ ∫ x : ℝ in a..b, g x :=
-- proof
  intervalIntegral.integral_mono h₀ h₂ h₁ h₃


-- created on 2026-09-26
