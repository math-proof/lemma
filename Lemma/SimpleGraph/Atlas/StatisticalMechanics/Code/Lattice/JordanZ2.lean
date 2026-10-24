import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanZ2
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[faceAdj_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma faceAdj_bottom_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (faceCorner00 a b) (faceCorner10 a b) := by
-- proof
  apply StatMech.Lattice.faceAdj_bottom a b

/--
[faceAdj_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma faceAdj_right_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (faceCorner10 a b) (faceCorner11 a b) := by
-- proof
  apply StatMech.Lattice.faceAdj_right a b

/--
[faceAdj_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma faceAdj_top_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (faceCorner11 a b) (faceCorner01 a b) := by
-- proof
  apply StatMech.Lattice.faceAdj_top a b

/--
[faceAdj_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma faceAdj_left_eq
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (faceCorner01 a b) (faceCorner00 a b) := by
-- proof
  apply StatMech.Lattice.faceAdj_left a b

/--
[bdInd_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma bdInd_comm_eq
  {S : Set (Site 2)}
  {x y : Site 2} :
-- imply
  bdInd S x y = bdInd S y x := by
-- proof
  apply StatMech.Lattice.bdInd_comm S x y

/--
[bdInd_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma bdInd_eq_one_iff_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj x y) :
-- imply
  bdInd S x y = 1 ↔ (x, y) ∈ edgeBoundary 2 S := by
-- proof
  apply StatMech.Lattice.bdInd_eq_one_iff S hadj

/--
[faceBoundaryDegree_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma faceBoundaryDegree_even_eq
  {S : Set (Site 2)}
  {a b : ℤ} :
-- imply
  faceBoundaryDegree S a b % 2 = 0 := by
-- proof
  apply StatMech.Lattice.faceBoundaryDegree_even S a b

/--
[faceBoundaryDegree_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma faceBoundaryDegree_le_four_eq
  {S : Set (Site 2)}
  {a b : ℤ} :
-- imply
  faceBoundaryDegree S a b ≤ 4 := by
-- proof
  apply StatMech.Lattice.faceBoundaryDegree_le_four S a b

/--
[isClosed_iff_dualEdge_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma isClosed_iff_dualEdge_isOpen_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Sym2 (Site 2)} :
-- imply
  ω e = false ↔ dualConfig ω (crossEdge e) = true := by
-- proof
  apply StatMech.Lattice.isClosed_iff_dualEdge_isOpen ω e

/--
[dualBoundaryDegree_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma dualBoundaryDegree_even_eq
  {S : Set (Site 2)}
  {a b : ℤ} :
-- imply
  faceBoundaryDegree S a b % 2 = 0 := by
-- proof
  apply StatMech.Lattice.dualBoundaryDegree_even S a b

/--
[crossEdge_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma crossEdge_bottom_eq
  {a b : ℤ} :
-- imply
  crossEdge s(faceCorner00 a b, faceCorner10 a b) = s(![-b, a], ![-b, a + 1]) := by
-- proof
  apply StatMech.Lattice.crossEdge_bottom a b

/--
[crossEdge_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma crossEdge_left_eq
  {a b : ℤ} :
-- imply
  crossEdge s(faceCorner01 a b, faceCorner00 a b) = s(![-(b + 1), a], ![-b, a]) := by
-- proof
  apply StatMech.Lattice.crossEdge_left a b

/--
[walk_mem_edgeBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma walk_mem_edgeBoundary_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  ∃ u v, (u, v) ∈ edgeBoundary 2 S := by
-- proof
  apply StatMech.Lattice.walk_mem_edgeBoundary S w hx hy

/--
[edgeBoundary_nonempty_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma edgeBoundary_nonempty_of_walk_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  (edgeBoundary 2 S).Nonempty := by
-- proof
  apply StatMech.Lattice.edgeBoundary_nonempty_of_walk S w hx hy

/--
[edge_leaving_cluster_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma edge_leaving_cluster_isClosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {x y : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj x y)
  (hx : x ∈ cluster 2 ω o)
  (hy : y ∉ cluster 2 ω o) :
-- imply
  ω s(x, y) = false := by
-- proof
  apply StatMech.Lattice.edge_leaving_cluster_isClosed o hadj hx hy

/--
[cluster_edgeBoundary_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma cluster_edgeBoundary_isClosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {x y : Site 2}
-- given
  (h : (x, y) ∈ edgeBoundary 2 (cluster 2 ω o)) :
-- imply
  ω s(x, y) = false := by
-- proof
  apply StatMech.Lattice.cluster_edgeBoundary_isClosed o h

/--
[cluster_edgeBoundary_crosses_dual_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean)
-/
@[path]
private lemma cluster_edgeBoundary_crosses_dual_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {o : Site 2}
  {x y : Site 2}
-- given
  (h : (x, y) ∈ edgeBoundary 2 (cluster 2 ω o)) :
-- imply
  dualConfig ω (crossEdge s(x, y)) = true := by
-- proof
  apply StatMech.Lattice.cluster_edgeBoundary_crosses_dual_open o h


-- created on 2026-10-23
