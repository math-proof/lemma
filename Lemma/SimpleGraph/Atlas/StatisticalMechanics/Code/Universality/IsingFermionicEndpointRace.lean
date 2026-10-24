import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace
open StatMech StatMech.Universality


/--
[lineFirstBoundary_partial_weight_le_fourth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean)
-/
@[path]
private lemma lineFirstBoundary_partial_weight_le_fourth_eq
  {m K : Nat}
-- given
  (hm : 0 < m) :
-- imply
  (∑ j ∈ Finset.range (K + 1), (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) / (2 : Real) ^ j) ≤ 3 * (K : Real) ^ 2 / (m : Real) ^ 4 := by
-- proof
  apply StatMech.Universality.lineFirstBoundary_partial_weight_le_fourth m K hm

/--
[endpointRace_sum_mul_eq_last_partial_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean)
-/
@[path]
private lemma endpointRace_sum_mul_eq_last_partial_add_eq
  {a b : Nat → Real}
  {N : Nat} :
-- imply
  (∑ k ∈ Finset.range (N + 1), a k * b k) = a N * (∑ k ∈ Finset.range (N + 1), b k) + ∑ k ∈ Finset.range N, (a k - a (k + 1)) * (∑ j ∈ Finset.range (k + 1), b j) := by
-- proof
  apply StatMech.Universality.endpointRace_sum_mul_eq_last_partial_add a b N

/--
[endpointBallot_firstBoundary_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean)
-/
@[path]
private lemma endpointBallot_firstBoundary_sum_le_eq
  {m N : Nat}
-- given
  (hm : 0 < m)
  (hN : N ≤ m * m) :
-- imply
  (∑ k ∈ Finset.range (N + 1), (4 / (k + 1 : Real)) * ((Nat.card (IsingLineFirstBoundaryFamily m k) : Real) / (2 : Real) ^ k)) ≤ 24 / (m : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.endpointBallot_firstBoundary_sum_le m N hm hN

/--
[endpointTransverseRaceWitness_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean)
-/
@[path]
private lemma endpointTransverseRaceWitness_weight_le_eq
  {m t : Nat}
  {level target : Int}
-- given
  (hm : 0 < m)
  (ht : t ≤ m * m) :
-- imply
  Nat.card (IsingEndpointTransverseRaceWitnessFamily m t level target) / (4 : Real) ^ t ≤ 24 / (m : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.endpointTransverseRaceWitness_weight_le m t level target hm ht

/--
[endpointTransverseRaceWitness_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean)
-/
@[path]
private lemma endpointTransverseRaceWitness_diffusive_weight_le_eq
  {rho m : Nat}
  {level target : Int}
-- given
  (hρ : 0 < rho)
  (hm : rho ≤ m) :
-- imply
  Nat.card (IsingEndpointTransverseRaceWitnessFamily m (rho * rho) level target) / (4 : Real) ^ (rho * rho) ≤ 24 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.endpointTransverseRaceWitness_diffusive_weight_le rho m level target hρ hm


-- created on 2026-10-23
