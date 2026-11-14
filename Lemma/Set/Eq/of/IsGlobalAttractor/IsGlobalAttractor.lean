import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import Lemma.Set.Subset.of.Attracts.IsClosed.Invariant
import Lemma.Set.PhaseBounded.of.IsGlobalAttractor


@[path]
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
  exact Set.Subset.antisymm (Set.Subset.of.Attracts.IsClosed.Invariant h₀.invariant h₁.compact.isClosed (h₁.attracts K (Set.PhaseBounded.of.IsGlobalAttractor h₀)))
    (Set.Subset.of.Attracts.IsClosed.Invariant h₁.invariant h₀.compact.isClosed (h₀.attracts K' (Set.PhaseBounded.of.IsGlobalAttractor h₁)))


-- created on 2026-09-26
