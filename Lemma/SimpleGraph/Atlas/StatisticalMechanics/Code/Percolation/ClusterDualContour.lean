import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.ClusterDualContour
open Finset Set SimpleGraph Function StatMech StatMech.Percolation


/--
[enclosingContourLinksExits_of_jordan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterDualContour.lean)
-/
@[path]
private lemma enclosingContourLinksExits_of_jordan_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hJordan : DiscreteJordanSeparation)
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hsame : ExitDartsSameOrbit ω hfin) :
-- imply
  EnclosingContourLinksExits ω hfin := by
-- proof
  apply StatMech.Percolation.enclosingContourLinksExits_of_jordan hJordan hfin hsame

/--
[finite_cluster_dual_circuit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterDualContour.lean)
-/
@[path]
private lemma finite_cluster_dual_circuit_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hJordan : DiscreteJordanSeparation)
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hsame : ExitDartsSameOrbit ω hfin) :
-- imply
  ∃ c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin), c.IsCycle ∧ ∃ w ∈ c.support, w 0 ≤ 0 := by
-- proof
  apply StatMech.Percolation.finite_cluster_dual_circuit hJordan hfin hsame

/--
[finite_cluster_dual_circuit_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterDualContour.lean)
-/
@[path]
private lemma finite_cluster_dual_circuit_separates_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hJordan : DiscreteJordanSeparation)
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hsame : ExitDartsSameOrbit ω hfin) :
-- imply
  (∃ c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin), c.IsCycle ∧ ∃ w ∈ c.support, w 0 ≤ 0) ∧ (∀ {z : Site 2}, z ∉ cluster 2 ω (origin 2) → ¬ (latticeMinusBarrier (cluster 2 ω (origin 2))).Reachable (origin 2) z) ∧ (∀ {z : Site 2}, z ∉ cluster 2 ω (origin 2) → ∀ w : (hypercubicLattice 2).Walk (origin 2) z, ¬ Even (crossCount (cluster 2 ω (origin 2)) w)) := by
-- proof
  apply StatMech.Percolation.finite_cluster_dual_circuit_separates hJordan hfin hsame

/--
[pcAnchoredEnclosure_of_jordan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterDualContour.lean)
-/
@[path]
private lemma pcAnchoredEnclosure_of_jordan_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hJordan : DiscreteJordanSeparation)
  (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), ExitDartsSameOrbit ω hfin) :
-- imply
  PcAnchoredEnclosure := by
-- proof
  apply StatMech.Percolation.pcAnchoredEnclosure_of_jordan hJordan hsame

/--
[pc_lt_one_of_jordan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterDualContour.lean)
-/
@[path]
private lemma pc_lt_one_of_jordan_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hJordan : DiscreteJordanSeparation)
  (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), ExitDartsSameOrbit ω hfin) :
-- imply
  pc 2 < 1 := by
-- proof
  apply StatMech.Percolation.pc_lt_one_of_jordan hJordan hsame

/--
[pc_pos_and_lt_one_of_jordan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterDualContour.lean)
-/
@[path]
private lemma pc_pos_and_lt_one_of_jordan_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hJordan : DiscreteJordanSeparation)
  (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), ExitDartsSameOrbit ω hfin) :
-- imply
  0 < pc 2 ∧ pc 2 < 1 := by
-- proof
  apply StatMech.Percolation.pc_pos_and_lt_one_of_jordan hJordan hsame


-- created on 2026-10-23
