import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.atsattachsurgery.Part4
open Finset Set SimpleGraph StatMech StatMech.Walls


/--
[ats_mem_insert_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_mem_insert_of_ne_eq
  {K : Finset (Site 2)}
  {c x : Site 2}
-- given
  (hx : x ≠ c) :
-- imply
  x ∈ (↑(insert c K) : Set (Site 2)) ↔ x ∈ (↑K : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.ats_mem_insert_of_ne hx

/--
[ats_bdEdge_insert_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_bdEdge_insert_of_notMem_eq
  {K : Finset (Site 2)}
  {c x y : Site 2}
-- given
  (hx : x ≠ c)
  (hy : y ≠ c) :
-- imply
  bdEdge (↑(insert c K) : Set (Site 2)) s(x, y) ↔ bdEdge (↑K : Set (Site 2)) s(x, y) := by
-- proof
  apply StatMech.Walls.ats_bdEdge_insert_of_notMem hx hy

/--
[ats_adj_insert_of_shared_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_adj_insert_of_shared_avoid_eq
  {K : Finset (Site 2)}
  {c f g u v : Site 2}
-- given
  (hshared : sharedPrimalEdge f g = s(u, v))
  (hu : u ≠ c)
  (hv : v ≠ c) :
-- imply
  (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj f g ↔ (faceBoundaryGraph (↑K : Set (Site 2))).Adj f g := by
-- proof
  apply StatMech.Walls.ats_adj_insert_of_shared_avoid hshared hu hv

/--
[ats_sharedPrimalEdge_corners_of_f](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_sharedPrimalEdge_corners_of_f_eq
  {f g : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj f g) :
-- imply
  ∃ u v : Site 2, sharedPrimalEdge f g = s(u, v) ∧ (u = ![f 0, f 1] ∨ u = ![f 0 + 1, f 1] ∨ u = ![f 0 + 1, f 1 + 1] ∨ u = ![f 0, f 1 + 1]) ∧ (v = ![f 0, f 1] ∨ v = ![f 0 + 1, f 1] ∨ v = ![f 0 + 1, f 1 + 1] ∨ v = ![f 0, f 1 + 1]) := by
-- proof
  apply StatMech.Walls.ats_sharedPrimalEdge_corners_of_f hadj

/--
[ats_adj_insert_iff_of_notCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_adj_insert_iff_of_notCorner_eq
  {K : Finset (Site 2)}
  {c f g : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj f g)
  (hc : ¬ ats_faceHasCorner c f) :
-- imply
  (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj f g ↔ (faceBoundaryGraph (↑K : Set (Site 2))).Adj f g := by
-- proof
  apply StatMech.Walls.ats_adj_insert_iff_of_notCorner hadj hc

/--
[ats_walk_transfer_of_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_walk_transfer_of_avoid_eq
  {K : Finset (Site 2)}
  {c a b : Site 2}
  {p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk a b}
-- given
  (havoid : ∀ w ∈ p.support, ¬ ats_faceHasCorner c w) :
-- imply
  ∃ q : (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Walk a b, q.support = p.support := by
-- proof
  apply StatMech.Walls.ats_walk_transfer_of_avoid p havoid

/--
[ats_walk_transfer_of_avoid'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_walk_transfer_of_avoid'_eq
  {K : Finset (Site 2)}
  {c a b : Site 2}
  {p : (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Walk a b}
-- given
  (havoid : ∀ w ∈ p.support, ¬ ats_faceHasCorner c w) :
-- imply
  ∃ q : (faceBoundaryGraph (↑K : Set (Site 2))).Walk a b, q.support = p.support := by
-- proof
  apply StatMech.Walls.ats_walk_transfer_of_avoid' p havoid

/--
[ats_reachable_insert_of_avoidWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_reachable_insert_of_avoidWalk_eq
  {K : Finset (Site 2)}
  {c a b : Site 2}
  {p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk a b}
-- given
  (havoid : ∀ w ∈ p.support, ¬ ats_faceHasCorner c w) :
-- imply
  (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable a b := by
-- proof
  apply StatMech.Walls.ats_reachable_insert_of_avoidWalk p havoid

/--
[ats_mem_support_insert_iff_of_notCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_mem_support_insert_iff_of_notCorner_eq
  {K : Finset (Site 2)}
  {c f : Site 2}
-- given
  (hc : ¬ ats_faceHasCorner c f) :
-- imply
  f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support ↔ f ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support := by
-- proof
  apply StatMech.Walls.ats_mem_support_insert_iff_of_notCorner hc

/--
[ats_attachStep_of_patch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_attachStep_of_patch_eq
-- given
  (h : ats_AttachPatch) :
-- imply
  fbc_AttachStep := by
-- proof
  apply StatMech.Walls.ats_attachStep_of_patch h

/--
[ats_faceHasCorner_iff_mem_cornerFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_faceHasCorner_iff_mem_cornerFaces_eq
  {c f : Site 2} :
-- imply
  ats_faceHasCorner c f ↔ f ∈ cornerFaces c := by
-- proof
  apply StatMech.Walls.ats_faceHasCorner_iff_mem_cornerFaces c f

/--
[ats_boundaryReachable_insert_of_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_boundaryReachable_insert_of_anchor_eq
  {K : Finset (Site 2)}
  {c : Site 2}
  {a₀ : Site 2}
-- given
  (hA : ∀ f : Site 2, ¬ ats_faceHasCorner c f → f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support → ∃ p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀, ∀ w ∈ p.support, ¬ ats_faceHasCorner c w)
  (hB : ∀ f : Site 2, ats_faceHasCorner c f → f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support → (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀) :
-- imply
  fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.ats_boundaryReachable_insert_of_anchor hA hB

/--
[ats_insert_domino_eq_tromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_insert_domino_eq_tromino_eq :
-- imply
  insert (![(0:ℤ), 1] : Site 2) ats_domino = pc2_tromino := by
-- proof
  apply StatMech.Walls.ats_insert_domino_eq_tromino

/--
[ats_domino_isConnectedCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_domino_isConnectedCluster_eq :
-- imply
  IsConnectedCluster ats_domino := by
-- proof
  apply StatMech.Walls.ats_domino_isConnectedCluster

/--
[ats_c_notMem_domino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_c_notMem_domino_eq :
-- imply
  (![(0:ℤ), 1] : Site 2) ∉ ats_domino := by
-- proof
  apply StatMech.Walls.ats_c_notMem_domino

/--
[ats_support_tromino_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_support_tromino_subset_eq :
-- imply
  (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).support ⊆ (pc2_tromFrame : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.ats_support_tromino_subset

/--
[ats_tromino_boundaryReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_tromino_boundaryReachable_eq :
-- imply
  fbc_BoundaryReachable (↑pc2_tromino : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.ats_tromino_boundaryReachable

/--
[ats_attachStep_witness_tromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean)
-/
@[path]
private lemma ats_attachStep_witness_tromino_eq :
-- imply
  (![(0:ℤ), 1] : Site 2) ∉ ats_domino ∧ IsConnectedCluster ats_domino ∧ insert (![(0:ℤ), 1] : Site 2) ats_domino = pc2_tromino ∧ IsConnectedCluster pc2_tromino ∧ fbc_BoundaryReachable (↑pc2_tromino : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.ats_attachStep_witness_tromino


-- created on 2026-10-23
