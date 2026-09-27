import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import sympy.dynamics.actor_critic
import sympy.Basic
open Filter


@[main]
private lemma main
  {α : Type*} [TopologicalSpace α] [T2Space α]
  {Φ : ContinuousSemiflow α}
  {K : Set α}
-- given
  (h₀ : K.Nonempty)
  (h₁ : IsCompact K)
  (h₂ : IsForwardInvariant Φ.toFun K) :
-- imply
  (omegaLimit atTop Φ.toFun K).Nonempty := by
-- proof
  exact nonempty_omegaLimit_of_isCompact_absorbing _ _ _ h₁ ⟨Set.Ici 0, Ici_mem_atTop 0, closure_minimal (Set.image2_subset_iff.2 fun _ ht _ hx => h₂ ht hx) h₁.isClosed⟩ h₀


-- created on 2026-09-26
