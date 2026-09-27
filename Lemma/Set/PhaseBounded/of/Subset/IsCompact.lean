import Mathlib.Topology.Order.Compact
import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {A : Type*} [Fintype A]
  {d : ℕ}
  {m : ℕ}
  {data : BoxedFiniteStateData S A d m}
  {B : Set (PhasePoint d m S)}
-- given
  (h₀ : IsCompact B)
  (h₁ : B ⊆ phase_space data) :
-- imply
  PhaseBounded data B := by
-- proof
  obtain ⟨M, hM⟩ := h₀.bddAbove_image (f := fun x : PhasePoint d m S => ‖x.2.1‖) (continuous_norm.comp (continuous_fst.comp continuous_snd)).continuousOn
  exact ⟨h₁, max M 0, le_max_right _ _, fun x hx => (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩


-- created on 2026-09-26
