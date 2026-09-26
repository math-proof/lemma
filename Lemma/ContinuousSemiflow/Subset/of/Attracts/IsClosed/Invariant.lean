import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.ContinuousSemiflow.OmegaLimitToFun.of.Attracts.IsClosed
import Lemma.ContinuousSemiflow.OmegaLimitToFun.of.Subset.Invariant
open Filter


@[main]
private lemma main
  {α : Type*} [TopologicalSpace α] [RegularSpace α]
  {Φ : ContinuousSemiflow α}
  {K : Set α}
  {B : Set α}
-- given
  (h₀ : Φ.Invariant K)
  (h₁ : IsClosed B)
  (h₂ : Φ.Attracts K B) :
-- imply
  K ⊆ B := by
-- proof
  exact (ContinuousSemiflow.OmegaLimitToFun.of.Subset.Invariant h₀ subset_rfl).trans (ContinuousSemiflow.OmegaLimitToFun.of.Attracts.IsClosed h₁ h₂)


-- created on 2026-09-26
