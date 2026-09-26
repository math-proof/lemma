import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import sympy.dynamics.actor_critic
import sympy.Basic
open Filter


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {A : Type*} [Fintype A]
  {d : ℕ}
  {m : ℕ}
  {data : BoxedFiniteStateData S A d m}
  {Φ : ContinuousSemiflow (PhasePoint d m S)}
  {K : Set (PhasePoint d m S)}
-- given
  (h₀ : IsCompact K)
  (h₁ : IsForwardInvariant Φ.toFun K)
  (h₂ : Φ.Absorbs data K) :
-- imply
  ∀ B, PhaseBounded data B → Φ.Attracts B (omegaLimit atTop Φ.toFun K) := by
-- proof
  intro B hB U hU hωU
  obtain ⟨u, hu, huU⟩ := eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset atTop Φ.toFun K h₀
    ((eventually_ge_atTop 0).mono fun t ht => h₁ ht) hU hωU
  obtain ⟨TU, hTU⟩ := mem_atTop_sets.1 hu
  obtain ⟨TB, hTB, hB'⟩ := h₂ B hB
  refine ⟨TB + max TU 0, add_nonneg hTB (le_max_right _ _), fun t ht x hx => ?_⟩
  have h₃ : Φ.toFun t x = Φ.toFun (t - TB) (Φ.toFun TB x) := by
    rw [← Φ.map_add' _ _ (by linarith [le_max_right TU 0]) hTB, sub_add_cancel]
  rw [h₃]
  exact huU (subset_closure ⟨t - TB, hTU _ (by linarith [le_max_left TU 0]), _, hB' TB le_rfl x hx, rfl⟩)


-- created on 2026-09-26
