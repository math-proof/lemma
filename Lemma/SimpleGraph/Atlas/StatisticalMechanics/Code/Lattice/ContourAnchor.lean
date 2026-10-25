import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[axisSite_zero_eq_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma axisSite_zero_eq_origin_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  axisSite 0 = origin 2 := by
-- proof
  apply StatMech.Lattice.axisSite_zero_eq_origin

/--
[axisSite_coord0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma axisSite_coord0_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {j : ℕ} :
-- imply
  axisSite j 0 = (j : ℤ) := by
-- proof
  apply StatMech.Lattice.axisSite_coord0 j

/--
[axisSite_coord1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma axisSite_coord1_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {j : ℕ} :
-- imply
  axisSite j 1 = 0 := by
-- proof
  apply StatMech.Lattice.axisSite_coord1 j

/--
[axisSite_zero_mem_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma axisSite_zero_mem_cluster_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  axisSite 0 ∈ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Lattice.axisSite_zero_mem_cluster

/--
[exists_axisSite_not_mem_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma exists_axisSite_not_mem_cluster_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ∃ j : ℕ, axisSite j ∉ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Lattice.exists_axisSite_not_mem_cluster hfin

/--
[axisSite_exit_succ_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma axisSite_exit_succ_not_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  axisSite (exitIndex (ω := ω) hfin + 1) ∉ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Lattice.axisSite_exit_succ_not_mem hfin

/--
[axisSite_lt_exit_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma axisSite_lt_exit_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {m : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hm : m < exitIndex (ω := ω) hfin) :
-- imply
  axisSite (m + 1) ∈ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Lattice.axisSite_lt_exit_mem hfin hm

/--
[axisSite_exit_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma axisSite_exit_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  axisSite (exitIndex (ω := ω) hfin) ∈ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Lattice.axisSite_exit_mem hfin

/--
[axisSite_exit_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma axisSite_exit_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (hypercubicLattice 2).Adj (axisSite (exitIndex (ω := ω) hfin)) (axisSite (exitIndex (ω := ω) hfin + 1)) := by
-- proof
  apply StatMech.Lattice.axisSite_exit_adj hfin

/--
[axisExitEdge_mem_edgeBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma axisExitEdge_mem_edgeBoundary_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (axisSite (exitIndex (ω := ω) hfin), axisSite (exitIndex (ω := ω) hfin + 1)) ∈ edgeBoundary 2 (cluster 2 ω (origin 2)) := by
-- proof
  apply StatMech.Lattice.axisExitEdge_mem_edgeBoundary hfin

/--
[axisExitEdge_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma axisExitEdge_isClosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ω s(axisSite (exitIndex (ω := ω) hfin), axisSite (exitIndex (ω := ω) hfin + 1)) = false := by
-- proof
  apply StatMech.Lattice.axisExitEdge_isClosed hfin

/--
[sharedPrimalEdge_exitFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma sharedPrimalEdge_exitFaces_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  sharedPrimalEdge (exitFaceUp (ω := ω) hfin) (exitFaceDown (ω := ω) hfin) = s(axisSite (exitIndex (ω := ω) hfin), axisSite (exitIndex (ω := ω) hfin + 1)) := by
-- proof
  apply StatMech.Lattice.sharedPrimalEdge_exitFaces hfin

/--
[exitFaces_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma exitFaces_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (hypercubicLattice 2).Adj (exitFaceUp (ω := ω) hfin) (exitFaceDown (ω := ω) hfin) := by
-- proof
  apply StatMech.Lattice.exitFaces_adj hfin

/--
[exitFaces_faceBoundaryGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma exitFaces_faceBoundaryGraph_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj (exitFaceUp (ω := ω) hfin) (exitFaceDown (ω := ω) hfin) := by
-- proof
  apply StatMech.Lattice.exitFaces_faceBoundaryGraph_adj hfin

/--
[exitFaceUp_mem_anchorFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma exitFaceUp_mem_anchorFinset_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {m : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hm : exitIndex (ω := ω) hfin < m) :
-- imply
  exitFaceUp (ω := ω) hfin ∈ anchorFinset m := by
-- proof
  apply StatMech.Lattice.exitFaceUp_mem_anchorFinset hfin hm

/--
[exitFaceDown_mem_anchorFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma exitFaceDown_mem_anchorFinset_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {m : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hm : exitIndex (ω := ω) hfin < m) :
-- imply
  exitFaceDown (ω := ω) hfin ∈ anchorFinset m := by
-- proof
  apply StatMech.Lattice.exitFaceDown_mem_anchorFinset hfin hm

/--
[exists_anchored_faceBoundary_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma exists_anchored_faceBoundary_edge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ∃ (j : ℕ) (f g : Site 2), (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj f g ∧ (∀ m : ℕ, j < m → f ∈ anchorFinset m ∧ g ∈ anchorFinset m) := by
-- proof
  apply StatMech.Lattice.exists_anchored_faceBoundary_edge hfin

/--
[exists_cycle_through_exitEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma exists_cycle_through_exitEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u), c.IsCycle ∧ s(exitFaceUp (ω := ω) hfin, exitFaceDown (ω := ω) hfin) ∈ c.edges := by
-- proof
  apply StatMech.Lattice.exists_cycle_through_exitEdge hfin

/--
[exists_cycle_based_exitFaceUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma exists_cycle_based_exitFaceUp_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ∃ (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin)), c.IsCycle := by
-- proof
  apply StatMech.Lattice.exists_cycle_based_exitFaceUp hfin

/--
[anchoredEnclosure_of_anchoredCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma anchoredEnclosure_of_anchoredCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hwind : AnchoredCycleExists ω hfin) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u), c.IsCycle ∧ u ∈ anchorFinset c.length := by
-- proof
  apply StatMech.Lattice.anchoredEnclosure_of_anchoredCycle hfin hwind

/--
[pcAnchoredEnclosure_of_anchoredCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean)
-/
@[path]
private lemma pcAnchoredEnclosure_of_anchoredCycle_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hwind : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), AnchoredCycleExists ω hfin) :
-- imply
  StatMech.Percolation.PcAnchoredEnclosure := by
-- proof
  apply StatMech.Lattice.pcAnchoredEnclosure_of_anchoredCycle hwind


-- created on 2026-10-23
