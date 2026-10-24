import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.LeftFace
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[leftAxisSite_zero_eq_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftAxisSite_zero_eq_origin_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  leftAxisSite 0 = origin 2 := by
-- proof
  apply StatMech.Lattice.leftAxisSite_zero_eq_origin

/--
[leftAxisSite_coord0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftAxisSite_coord0_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {k : ℕ} :
-- imply
  leftAxisSite k 0 = -(k : ℤ) := by
-- proof
  apply StatMech.Lattice.leftAxisSite_coord0 k

/--
[leftAxisSite_coord1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftAxisSite_coord1_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {k : ℕ} :
-- imply
  leftAxisSite k 1 = 0 := by
-- proof
  apply StatMech.Lattice.leftAxisSite_coord1 k

/--
[leftAxisSite_zero_mem_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftAxisSite_zero_mem_cluster_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  leftAxisSite 0 ∈ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Lattice.leftAxisSite_zero_mem_cluster

/--
[exists_leftAxisSite_not_mem_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma exists_leftAxisSite_not_mem_cluster_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ∃ k : ℕ, leftAxisSite k ∉ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Lattice.exists_leftAxisSite_not_mem_cluster hfin

/--
[leftAxisSite_exit_succ_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftAxisSite_exit_succ_not_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  leftAxisSite (leftExitIndex (ω := ω) hfin + 1) ∉ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Lattice.leftAxisSite_exit_succ_not_mem hfin

/--
[leftAxisSite_lt_exit_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftAxisSite_lt_exit_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {m : ℕ}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (hm : m < leftExitIndex (ω := ω) hfin) :
-- imply
  leftAxisSite (m + 1) ∈ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Lattice.leftAxisSite_lt_exit_mem hfin hm

/--
[leftAxisSite_exit_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftAxisSite_exit_mem_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  leftAxisSite (leftExitIndex (ω := ω) hfin) ∈ cluster 2 ω (origin 2) := by
-- proof
  apply StatMech.Lattice.leftAxisSite_exit_mem hfin

/--
[leftAxisSite_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftAxisSite_eq_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {k : ℕ} :
-- imply
  (leftAxisSite k : Site 2) = ![-(k : ℤ), 0] := by
-- proof
  apply StatMech.Lattice.leftAxisSite_eq k

/--
[leftAxisSite_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftAxisSite_succ_eq_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {k : ℕ} :
-- imply
  (leftAxisSite (k + 1) : Site 2) = ![-(k : ℤ) - 1, 0] := by
-- proof
  apply StatMech.Lattice.leftAxisSite_succ_eq k

/--
[leftAxisSite_exit_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftAxisSite_exit_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (hypercubicLattice 2).Adj (leftAxisSite (leftExitIndex (ω := ω) hfin)) (leftAxisSite (leftExitIndex (ω := ω) hfin + 1)) := by
-- proof
  apply StatMech.Lattice.leftAxisSite_exit_adj hfin

/--
[leftExitEdge_mem_edgeBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftExitEdge_mem_edgeBoundary_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (leftAxisSite (leftExitIndex (ω := ω) hfin), leftAxisSite (leftExitIndex (ω := ω) hfin + 1)) ∈ edgeBoundary 2 (cluster 2 ω (origin 2)) := by
-- proof
  apply StatMech.Lattice.leftExitEdge_mem_edgeBoundary hfin

/--
[leftExitEdge_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftExitEdge_isClosed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ω s(leftAxisSite (leftExitIndex (ω := ω) hfin), leftAxisSite (leftExitIndex (ω := ω) hfin + 1)) = false := by
-- proof
  apply StatMech.Lattice.leftExitEdge_isClosed hfin

/--
[leftExitFaceUp_coord0_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftExitFaceUp_coord0_nonpos_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  leftExitFaceUp (ω := ω) hfin 0 ≤ 0 := by
-- proof
  apply StatMech.Lattice.leftExitFaceUp_coord0_nonpos hfin

/--
[leftExitFaceDown_coord0_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftExitFaceDown_coord0_nonpos_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  leftExitFaceDown (ω := ω) hfin 0 ≤ 0 := by
-- proof
  apply StatMech.Lattice.leftExitFaceDown_coord0_nonpos hfin

/--
[sharedPrimalEdge_leftExitFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma sharedPrimalEdge_leftExitFaces_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  sharedPrimalEdge (leftExitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) = s(leftAxisSite (leftExitIndex (ω := ω) hfin), leftAxisSite (leftExitIndex (ω := ω) hfin + 1)) := by
-- proof
  apply StatMech.Lattice.sharedPrimalEdge_leftExitFaces hfin

/--
[leftExitFaces_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftExitFaces_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (hypercubicLattice 2).Adj (leftExitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) := by
-- proof
  apply StatMech.Lattice.leftExitFaces_adj hfin

/--
[leftExitFaces_faceBoundaryGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma leftExitFaces_faceBoundaryGraph_adj_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj (leftExitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) := by
-- proof
  apply StatMech.Lattice.leftExitFaces_faceBoundaryGraph_adj hfin

/--
[exists_faceBoundaryGraph_leftEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma exists_faceBoundaryGraph_leftEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ∃ f g : Site 2, (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj f g ∧ f 0 ≤ 0 ∧ g 0 ≤ 0 := by
-- proof
  apply StatMech.Lattice.exists_faceBoundaryGraph_leftEdge hfin

/--
[exists_cycle_through_leftEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma exists_cycle_through_leftEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u), c.IsCycle ∧ s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈ c.edges := by
-- proof
  apply StatMech.Lattice.exists_cycle_through_leftEdge hfin

/--
[cycleHasLeftFace_of_cycle_through_exitFaceUp_and_leftFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma cycleHasLeftFace_of_cycle_through_exitFaceUp_and_leftFace_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (h : ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u), c.IsCycle ∧ exitFaceUp (ω := ω) hfin ∈ c.support ∧ ∃ w ∈ c.support, w 0 ≤ 0) :
-- imply
  CycleHasLeftFace ω hfin := by
-- proof
  apply StatMech.Lattice.cycleHasLeftFace_of_cycle_through_exitFaceUp_and_leftFace hfin h

/--
[cycleHasLeftFace_of_exitFaceUp_cycle_through_leftEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma cycleHasLeftFace_of_exitFaceUp_cycle_through_leftEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin))
  (hcyc : c.IsCycle)
  (hedge : s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈ c.edges) :
-- imply
  CycleHasLeftFace ω hfin := by
-- proof
  apply StatMech.Lattice.cycleHasLeftFace_of_exitFaceUp_cycle_through_leftEdge hfin c hcyc hedge

/--
[anchoredCycleExists_of_exitFaceUp_cycle_through_leftEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma anchoredCycleExists_of_exitFaceUp_cycle_through_leftEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin))
  (hcyc : c.IsCycle)
  (hedge : s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈ c.edges) :
-- imply
  AnchoredCycleExists ω hfin := by
-- proof
  apply StatMech.Lattice.anchoredCycleExists_of_exitFaceUp_cycle_through_leftEdge hfin c hcyc hedge

/--
[pcAnchoredEnclosure_of_exitFaceUp_cycle_through_leftEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean)
-/
@[path]
private lemma pcAnchoredEnclosure_of_exitFaceUp_cycle_through_leftEdge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite), ∃ c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin), c.IsCycle ∧ s(leftExitFaceUp (ω := ω) hfin, leftExitFaceDown (ω := ω) hfin) ∈ c.edges) :
-- imply
  StatMech.Percolation.PcAnchoredEnclosure := by
-- proof
  apply StatMech.Lattice.pcAnchoredEnclosure_of_exitFaceUp_cycle_through_leftEdge h


-- created on 2026-10-23
