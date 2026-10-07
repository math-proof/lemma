import Mathlib.Dynamics.OmegaLimit
import sympy.Basic
open Filter


@[main]
private lemma main
  {α : Type*} [TopologicalSpace α]
  {β : Type*} [TopologicalSpace β]
-- given
  (ϕ : ℝ → α → β)
  (K : Set α)
  (y : β) :
-- imply
  y ∈ omegaLimit atTop ϕ K ↔ ∀ T, y ∈ closure (Set.image2 ϕ (Set.Ici T) K) := by
-- proof
  simp only [omegaLimit_def, Set.mem_iInter]
  constructor
  · intro h T
    exact h _ (Ici_mem_atTop T)
  · intro h u hu
    obtain ⟨T, hT⟩ := mem_atTop_sets.1 hu
    exact closure_mono (Set.image2_subset_right fun t ht => hT t ht) (h T)


-- created on 2026-09-26
