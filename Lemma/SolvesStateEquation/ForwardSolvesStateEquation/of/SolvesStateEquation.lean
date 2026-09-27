import sympy.dynamics.actor_critic
import sympy.Basic
open Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {d : ℕ}
  {δ : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {θ : ℝ → EuclideanVec d}
  {μ : ℝ → S → ℝ}
-- given
  (h₀ : SolvesStateEquation δ Q θ μ) :
-- imply
  ForwardSolvesStateEquation δ Q θ μ := by
-- proof
  exact ⟨continuous_iff_continuousAt.2 fun t => (h₀.hasDeriv t).continuousAt, fun t _ => (h₀.hasDeriv t).hasDerivWithinAt⟩


-- created on 2026-09-26
