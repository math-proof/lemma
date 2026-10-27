import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
open Set SimpleGraph StatMech StatMech.Lattice


/--
[ooi_odd_of_connected_to_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitInteriorOdd.lean)
-/
@[path]
private lemma ooi_odd_of_connected_to_odd_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z z0 : Site 2}
  {p : (hypercubicLattice 2).Walk z z0}
-- given
  (hp : ∀ w ∈ p.support, w ∉ Vc.support)
  (hodd : ¬ Even (jec_rayCount z0 Vc)) :
-- imply
  ¬ Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Lattice.ooi_odd_of_connected_to_odd Vc p hp hodd

/--
[ooi_insideHalf_of_oddWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitInteriorOdd.lean)
-/
@[path]
private lemma ooi_insideHalf_of_oddWitness_eq
  {K : Set (Site 2)}
  {e : Dart}
  {z0 : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop K hK e he)))
  (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support)) :
-- imply
  ∀ z, z ∈ K → ¬ Even (jec_rayCount z (olb_orbitLoop K hK e he)) := by
-- proof
  apply StatMech.Lattice.ooi_insideHalf_of_oddWitness K hK e he hodd0 hInt

/--
[ooi_orbitIsLoop_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitInteriorOdd.lean)
-/
@[path]
private lemma ooi_orbitIsLoop_of_witness_eq
  {K : Set (Site 2)}
  {e : Dart}
  {z0 : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧ (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0))
  (_hz0K : z0 ∈ K)
  (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop K hK e he)))
  (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support)) :
-- imply
  ccs_OrbitIsLoop K := by
-- proof
  apply StatMech.Lattice.ooi_orbitIsLoop_of_witness K hK e he hExt _hz0K hodd0 hInt


-- created on 2026-10-23
