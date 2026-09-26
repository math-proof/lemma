import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.ContinuousSemiflow.Subset.of.Attracts.IsClosed.Invariant
import Lemma.IsGlobalAttractor.PhaseBounded.of.IsGlobalAttractor


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {A : Type*} [Fintype A]
  {d : ℕ}
  {m : ℕ}
  {data : BoxedFiniteStateData S A d m}
  {Φ : ContinuousSemiflow (PhasePoint d m S)}
  {K : Set (PhasePoint d m S)}
  {K' : Set (PhasePoint d m S)}
-- given
  (h₀ : IsGlobalAttractor data Φ K)
  (h₁ : IsGlobalAttractor data Φ K') :
-- imply
  K = K' := by
-- proof
  exact Set.Subset.antisymm (ContinuousSemiflow.Subset.of.Attracts.IsClosed.Invariant h₀.invariant h₁.compact.isClosed (h₁.attracts K (IsGlobalAttractor.PhaseBounded.of.IsGlobalAttractor h₀)))
    (ContinuousSemiflow.Subset.of.Attracts.IsClosed.Invariant h₁.invariant h₀.compact.isClosed (h₀.attracts K' (IsGlobalAttractor.PhaseBounded.of.IsGlobalAttractor h₁)))


-- created on 2026-09-26
