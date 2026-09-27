import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {S : Type*} [Fintype S]
  [Nonempty S]
  {A : Type*} [Fintype A]
  {d : ℕ}
  {m : ℕ}
  {data : BoxedFiniteStateData S A d m}
  {rW : ℝ}
-- given
  (h₀ : 0 ≤ data.rTheta)
  (h₁ : 0 ≤ rW) :
-- imply
  (absorbing_set data rW).Nonempty := by
-- proof
  exact ⟨(0, 0, uniform_distribution), fun j => by simpa using h₀, by simpa using h₁, show StochasticVec _ from inferInstance⟩


-- created on 2026-09-26
