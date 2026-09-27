import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.ContinuousSemiflow.OmegaLimitToFun.of.IsForwardInvariantToFun.IsClosed
import Lemma.ContinuousSemiflow.IsCompact_OmegaLimitToFun.of.IsForwardInvariantToFun.IsCompact
import Lemma.ContinuousSemiflow.InvariantOmegaLimitToFun.of.IsForwardInvariantToFun.IsCompact
import Lemma.ContinuousSemiflow.All_AttractsOmegaLimitToFun.of.Absorbs.IsForwardInvariantToFun.IsCompact
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
  (h₁ : K ⊆ phase_space data)
  (h₂ : IsForwardInvariant Φ.toFun K)
  (h₃ : Φ.Absorbs data K) :
-- imply
  IsGlobalAttractor data Φ (omegaLimit atTop Φ.toFun K) := by
-- proof
  exact ⟨ContinuousSemiflow.IsCompact_OmegaLimitToFun.of.IsForwardInvariantToFun.IsCompact h₀ h₂, (ContinuousSemiflow.OmegaLimitToFun.of.IsForwardInvariantToFun.IsClosed h₀.isClosed h₂).trans h₁, ContinuousSemiflow.InvariantOmegaLimitToFun.of.IsForwardInvariantToFun.IsCompact h₀ h₂, ContinuousSemiflow.All_AttractsOmegaLimitToFun.of.Absorbs.IsForwardInvariantToFun.IsCompact h₀ h₂ h₃⟩


-- created on 2026-09-26
