import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import sympy.dynamics.actor_critic
import sympy.Basic


@[main]
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
