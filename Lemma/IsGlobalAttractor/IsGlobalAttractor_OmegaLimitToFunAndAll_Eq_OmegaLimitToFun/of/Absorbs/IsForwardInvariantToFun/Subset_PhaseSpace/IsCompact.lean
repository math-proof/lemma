import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.IsGlobalAttractor.Eq.of.IsGlobalAttractor.IsGlobalAttractor
import Lemma.IsGlobalAttractor.IsGlobalAttractor_OmegaLimitToFun.of.Absorbs.IsForwardInvariantToFun.Subset_PhaseSpace.IsCompact
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
  IsGlobalAttractor data Φ (omegaLimit atTop Φ.toFun K) ∧ ∀ K', IsGlobalAttractor data Φ K' → K' = omegaLimit atTop Φ.toFun K := by
-- proof
  exact ⟨IsGlobalAttractor.IsGlobalAttractor_OmegaLimitToFun.of.Absorbs.IsForwardInvariantToFun.Subset_PhaseSpace.IsCompact h₀ h₁ h₂ h₃, fun _ h => IsGlobalAttractor.Eq.of.IsGlobalAttractor.IsGlobalAttractor h (IsGlobalAttractor.IsGlobalAttractor_OmegaLimitToFun.of.Absorbs.IsForwardInvariantToFun.Subset_PhaseSpace.IsCompact h₀ h₁ h₂ h₃)⟩


-- created on 2026-09-26
