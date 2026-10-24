import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.FaceRegion
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[mem_bdEdgeSet2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma mem_bdEdgeSet2_eq
  {S : Set (Site 2)}
  {x y : Site 2} :
-- imply
  s(x, y) ∈ bdEdgeSet2 S ↔ (x ∈ S ↔ y ∉ S) := by
-- proof
  apply StatMech.Lattice.mem_bdEdgeSet2 S x y

/--
[cutLattice_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma cutLattice_adj_eq
  {S : Set (Site 2)}
  {x y : Site 2} :
-- imply
  (cutLattice S).Adj x y ↔ (hypercubicLattice 2).Adj x y ∧ s(x, y) ∉ bdEdgeSet2 S := by
-- proof
  apply StatMech.Lattice.cutLattice_adj S x y

/--
[cutLattice_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma cutLattice_le_eq
  {S : Set (Site 2)} :
-- imply
  cutLattice S ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.cutLattice_le S

/--
[cutLattice_adj_of_both_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma cutLattice_adj_of_both_mem_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj x y)
  (hx : x ∈ S)
  (hy : y ∈ S) :
-- imply
  (cutLattice S).Adj x y := by
-- proof
  apply StatMech.Lattice.cutLattice_adj_of_both_mem S hadj hx hy

/--
[cutLattice_adj_preserves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma cutLattice_adj_preserves_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hadj : (cutLattice S).Adj x y)
  (hx : x ∈ S) :
-- imply
  y ∈ S := by
-- proof
  apply StatMech.Lattice.cutLattice_adj_preserves S hadj hx

/--
[cutLattice_walk_preserves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma cutLattice_walk_preserves_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (cutLattice S).Walk x y}
-- given
  (hx : x ∈ S) :
-- imply
  y ∈ S := by
-- proof
  apply StatMech.Lattice.cutLattice_walk_preserves S w hx

/--
[cutLattice_reachable_preserves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma cutLattice_reachable_preserves_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (h : (cutLattice S).Reachable x y)
  (hx : x ∈ S) :
-- imply
  y ∈ S := by
-- proof
  apply StatMech.Lattice.cutLattice_reachable_preserves S h hx

/--
[cutLattice_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma cutLattice_not_reachable_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  ¬ (cutLattice S).Reachable x y := by
-- proof
  apply StatMech.Lattice.cutLattice_not_reachable S hx hy

/--
[openWalk_to_cutLattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma openWalk_to_cutLattice_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {x y : Site 2}
  {w : (openSubgraph 2 ω).Walk x y}
-- given
  (hx : x ∈ cluster 2 ω o) :
-- imply
  (cutLattice (cluster 2 ω o)).Reachable x y := by
-- proof
  apply StatMech.Lattice.openWalk_to_cutLattice o w hx

/--
[cutLattice_reachable_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma cutLattice_reachable_of_connected_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {x : Site 2}
-- given
  (hx : x ∈ cluster 2 ω o) :
-- imply
  (cutLattice (cluster 2 ω o)).Reachable o x := by
-- proof
  apply StatMech.Lattice.cutLattice_reachable_of_connected o hx

/--
[mem_insideRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma mem_insideRegion_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o x : Site 2} :
-- imply
  x ∈ insideRegion ω o ↔ (cutLattice (cluster 2 ω o)).Reachable o x := by
-- proof
  apply StatMech.Lattice.mem_insideRegion

/--
[insideRegion_eq_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma insideRegion_eq_cluster_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2} :
-- imply
  insideRegion ω o = cluster 2 ω o := by
-- proof
  apply StatMech.Lattice.insideRegion_eq_cluster o

/--
[origin_mem_insideRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma origin_mem_insideRegion_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2} :
-- imply
  o ∈ insideRegion ω o := by
-- proof
  apply StatMech.Lattice.origin_mem_insideRegion o

/--
[insideRegion_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma insideRegion_finite_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
-- given
  (hfin : (cluster 2 ω o).Finite) :
-- imply
  (insideRegion ω o).Finite := by
-- proof
  apply StatMech.Lattice.insideRegion_finite o hfin

/--
[exists_outside_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma exists_outside_far_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {n : ℕ}
-- given
  (hS : S.Finite) :
-- imply
  ∃ x : Site 2, x ∉ box 2 n ∧ x ∉ S := by
-- proof
  apply StatMech.Lattice.exists_outside_far S hS n

/--
[exists_outsideRegion_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma exists_outsideRegion_far_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {n : ℕ}
-- given
  (hfin : (cluster 2 ω o).Finite) :
-- imply
  ∃ x : Site 2, x ∉ box 2 n ∧ x ∉ insideRegion ω o := by
-- proof
  apply StatMech.Lattice.exists_outsideRegion_far o hfin n

/--
[origin_separated_from_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma origin_separated_from_outside_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {z : Site 2}
-- given
  (hz : z ∉ cluster 2 ω o) :
-- imply
  ¬ (cutLattice (cluster 2 ω o)).Reachable o z := by
-- proof
  apply StatMech.Lattice.origin_separated_from_outside o hz

/--
[origin_separated_from_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma origin_separated_from_far_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {n : ℕ}
-- given
  (hfin : (cluster 2 ω o).Finite) :
-- imply
  ∃ z : Site 2, z ∉ box 2 n ∧ ¬ (cutLattice (cluster 2 ω o)).Reachable o z := by
-- proof
  apply StatMech.Lattice.origin_separated_from_far o hfin n

/--
[exists_two_cutComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma exists_two_cutComponents_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
-- given
  (hfin : (cluster 2 ω o).Finite) :
-- imply
  ∃ z : Site 2, (cutLattice (cluster 2 ω o)).connectedComponentMk z ≠ (cutLattice (cluster 2 ω o)).connectedComponentMk o := by
-- proof
  apply StatMech.Lattice.exists_two_cutComponents o hfin

/--
[bdEdgeSet2_to_edgeBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma bdEdgeSet2_to_edgeBoundary_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj x y)
  (hmem : s(x, y) ∈ bdEdgeSet2 S) :
-- imply
  (x, y) ∈ edgeBoundary 2 S := by
-- proof
  apply StatMech.Lattice.bdEdgeSet2_to_edgeBoundary S hadj hmem

/--
[cluster_cutEdge_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma cluster_cutEdge_isClosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {x y : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj x y)
  (hmem : s(x, y) ∈ bdEdgeSet2 (cluster 2 ω o)) :
-- imply
  ω s(x, y) = false := by
-- proof
  apply StatMech.Lattice.cluster_cutEdge_isClosed o hadj hmem

/--
[cluster_cutEdge_crosses_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma cluster_cutEdge_crosses_dual_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {x y : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj x y)
  (hmem : s(x, y) ∈ bdEdgeSet2 (cluster 2 ω o)) :
-- imply
  dualConfig ω (crossEdge s(x, y)) = true := by
-- proof
  apply StatMech.Lattice.cluster_cutEdge_crosses_dual_open o hadj hmem

/--
[cluster_isBoundedRegion_separated_by_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean)
-/
@[path]
private lemma cluster_isBoundedRegion_separated_by_boundary_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {z₀ : Site 2}
  {w : (hypercubicLattice 2).Walk o z₀}
-- given
  (hfin : (cluster 2 ω o).Finite)
  (hz₀ : z₀ ∉ cluster 2 ω o) :
-- imply
  (insideRegion ω o = cluster 2 ω o ∧ (insideRegion ω o).Finite) ∧ (∀ z ∉ cluster 2 ω o, ¬ (cutLattice (cluster 2 ω o)).Reachable o z) ∧ (∀ n : ℕ, ∃ z : Site 2, z ∉ box 2 n ∧ ¬ (cutLattice (cluster 2 ω o)).Reachable o z) ∧ (∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle) := by
-- proof
  apply StatMech.Lattice.cluster_isBoundedRegion_separated_by_boundary o hfin w hz₀


-- created on 2026-10-23
