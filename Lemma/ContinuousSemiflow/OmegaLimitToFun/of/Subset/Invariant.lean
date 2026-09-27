import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.OmegaLimit.In_OmegaLimit.is.All_In_Closure_Image2_Ici
open Filter


@[main]
private lemma main
  {α : Type*} [TopologicalSpace α]
  {Φ : ContinuousSemiflow α}
  {B : Set α}
  {K : Set α}
-- given
  (h₀ : Φ.Invariant B)
  (h₁ : B ⊆ K) :
-- imply
  B ⊆ omegaLimit atTop Φ.toFun K := by
-- proof
  intro y hy
  refine (OmegaLimit.In_OmegaLimit.is.All_In_Closure_Image2_Ici Φ.toFun K y).2 fun T => ?_
  have h : y ∈ Φ.toFun (max T 0) '' B := by
    rw [h₀ _ (le_max_right _ _)]
    exact hy
  obtain ⟨z, hz, rfl⟩ := h
  exact subset_closure ⟨max T 0, Set.mem_Ici.2 (le_max_left _ _), z, h₁ hz, rfl⟩


-- created on 2026-09-26
