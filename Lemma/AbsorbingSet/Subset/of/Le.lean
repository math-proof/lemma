import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {A : Type*} [Fintype A]
  {d : ℕ}
  {m : ℕ}
  {data : BoxedFiniteStateData S A d m}
  {r : ℝ}
  {r' : ℝ}
-- given
  (h₀ : r ≤ r') :
-- imply
  absorbing_set data r ⊆ absorbing_set data r' := by
-- proof
  exact fun _ hx => ⟨hx.1, Metric.closedBall_subset_closedBall h₀ hx.2.1, hx.2.2⟩


-- created on 2026-09-26
