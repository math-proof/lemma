import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {lambdaC : ℝ}
  {Bb : ℝ}
-- given
  (h₀ : 0 < lambdaC)
  (h₁ : 0 ≤ Bb) :
-- imply
  IsValidCriticRadius lambdaC Bb (critic_radius Bb lambdaC) := by
-- proof
  exact ⟨h₀, h₁, le_max_left _ _, le_max_right _ _⟩


-- created on 2026-09-26
