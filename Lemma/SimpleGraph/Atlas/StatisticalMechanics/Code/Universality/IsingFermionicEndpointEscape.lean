import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
open StatMech StatMech.Universality


/--
[isingLineStoppedMean_farFifth_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean)
-/
@[path]
private lemma isingLineStoppedMean_farFifth_le_eq
  {m t : Nat}
  {p : IsingLineBox m} :
-- imply
  isingLineStoppedMean m t (isingLineFarFifth m) p ≤ ((m : Real) - (p.1 : Real)) ^ 5 + 10 * (t : Real) * ((m : Real) - (p.1 : Real)) ^ 3 + 15 * (t : Real) ^ 2 * ((m : Real) - (p.1 : Real)) := by
-- proof
  apply StatMech.Universality.isingLineStoppedMean_farFifth_le m t p

/--
[isingLineStoppedKernel_far_boundary_le_fifth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean)
-/
@[path]
private lemma isingLineStoppedKernel_far_boundary_le_fifth_eq
  {m t : Nat}
-- given
  (hm : 0 < m) :
-- imply
  isingLineStoppedKernel m t ⟨m - 1, by omega⟩ ⟨0, by omega⟩ ≤ 26 * (t + 1 : Real) ^ 2 / (m : Real) ^ 5 := by
-- proof
  apply StatMech.Universality.isingLineStoppedKernel_far_boundary_le_fifth m t hm

/--
[lineFarFirstBoundary_partial_weight_le_fifth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean)
-/
@[path]
private lemma lineFarFirstBoundary_partial_weight_le_fifth_eq
  {m K : Nat}
-- given
  (hm : 0 < m) :
-- imply
  (∑ j ∈ Finset.range (K + 1), (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) / (2 : Real) ^ j) ≤ 26 * (K + 1 : Real) ^ 2 / (m : Real) ^ 5 := by
-- proof
  apply StatMech.Universality.lineFarFirstBoundary_partial_weight_le_fifth m K hm

/--
[endpointKernel_farFirstBoundary_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean)
-/
@[path]
private lemma endpointKernel_farFirstBoundary_sum_le_eq
  {m N : Nat}
-- given
  (hm : 0 < m)
  (hN : N ≤ m * m) :
-- imply
  (∑ k ∈ Finset.range (N + 1), (2 / Real.sqrt (k + 1 : Real)) * ((Nat.card (IsingLineFarFirstBoundaryFamily m k) : Real) / (2 : Real) ^ k)) ≤ 468 / (m : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.endpointKernel_farFirstBoundary_sum_le m N hm hN

/--
[endpointFarEscapeWitness_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean)
-/
@[path]
private lemma endpointFarEscapeWitness_weight_le_eq
  {m t : Nat}
  {start target : Int}
-- given
  (hm : 0 < m)
  (ht : t ≤ m * m) :
-- imply
  Nat.card (IsingEndpointFarEscapeWitnessFamily m t start target) / (4 : Real) ^ t ≤ 468 / (m : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.endpointFarEscapeWitness_weight_le m t start target hm ht

/--
[endpointFarEscapeWitness_diffusive_weight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean)
-/
@[path]
private lemma endpointFarEscapeWitness_diffusive_weight_le_eq
  {rho m : Nat}
  {start target : Int}
-- given
  (hρ : 0 < rho)
  (hm : rho ≤ m) :
-- imply
  Nat.card (IsingEndpointFarEscapeWitnessFamily m (rho * rho) start target) / (4 : Real) ^ (rho * rho) ≤ 468 / (rho : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.endpointFarEscapeWitness_diffusive_weight_le rho m start target hρ hm


-- created on 2026-10-23
