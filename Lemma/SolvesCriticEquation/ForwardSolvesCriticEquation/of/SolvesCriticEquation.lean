import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {m : ℕ}
  {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
  {b : ℝ → EuclideanVec m}
  {w : ℝ → EuclideanVec m}
-- given
  (h₀ : SolvesCriticEquation A b w) :
-- imply
  ForwardSolvesCriticEquation A b w := by
-- proof
  exact ⟨continuous_iff_continuousAt.2 fun t => (h₀.hasDeriv t).continuousAt, fun t _ => (h₀.hasDeriv t).hasDerivWithinAt⟩


-- created on 2026-09-26
