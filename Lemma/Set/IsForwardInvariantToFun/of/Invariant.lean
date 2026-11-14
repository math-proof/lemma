import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import Structure.Dynamics.ActorCritic.Part6
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {α : Type*} [TopologicalSpace α]
  {Φ : ContinuousSemiflow α}
  {K : Set α}
-- given
  (h₀ : Φ.Invariant K) :
-- imply
  IsForwardInvariant Φ.toFun K := by
-- proof
  exact fun t ht x hx => h₀ t ht ▸ ⟨x, hx, rfl⟩


-- created on 2026-09-26
