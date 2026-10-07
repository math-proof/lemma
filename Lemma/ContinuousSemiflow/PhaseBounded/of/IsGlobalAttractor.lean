import sympy.dynamics.actor_critic
import sympy.Basic
import Lemma.Set.PhaseBounded.of.Subset.IsCompact


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
  (h₀ : IsGlobalAttractor data Φ K) :
-- imply
  PhaseBounded data K := by
-- proof
  exact Set.PhaseBounded.of.Subset.IsCompact h₀.compact h₀.subset


-- created on 2026-09-26
