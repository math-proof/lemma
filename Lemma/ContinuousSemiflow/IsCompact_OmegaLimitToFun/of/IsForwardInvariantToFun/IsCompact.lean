import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.ContinuousSemiflow.OmegaLimitToFun.of.IsForwardInvariantToFun.IsClosed
open Filter


@[main]
private lemma main
  {α : Type*} [TopologicalSpace α] [T2Space α]
  {Φ : ContinuousSemiflow α}
  {K : Set α}
-- given
  (h₀ : IsCompact K)
  (h₁ : IsForwardInvariant Φ.toFun K) :
-- imply
  IsCompact (omegaLimit atTop Φ.toFun K) := by
-- proof
  exact h₀.of_isClosed_subset (isClosed_omegaLimit _ _ _) (ContinuousSemiflow.OmegaLimitToFun.of.IsForwardInvariantToFun.IsClosed h₀.isClosed h₁)


-- created on 2026-09-26
