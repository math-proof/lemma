import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {d : ℕ}
  {r : ℝ}
  {θ : ℝ → EuclideanVec d}
  {h : ℝ → EuclideanVec d}
-- given
  (h₀ : SolvesActorBoxEquation r θ h) :
-- imply
  ForwardSolvesActorBoxEquation r θ h := by
-- proof
  exact ⟨h₀.cont_theta, h₀.cont_h, fun t j _ => (h₀.hasDeriv t j).hasDerivWithinAt⟩


-- created on 2026-09-26
