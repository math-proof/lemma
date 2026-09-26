import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {A : Type*} [Fintype A]
  {d : ℕ}
  {m : ℕ}
  {data : BoxedFiniteStateData S A d m}
-- given
  (rW : ℝ) :
-- imply
  absorbing_set data rW ⊆ phase_space data := by
-- proof
  exact fun _ hx => ⟨hx.1, hx.2.2⟩


-- created on 2026-09-26
