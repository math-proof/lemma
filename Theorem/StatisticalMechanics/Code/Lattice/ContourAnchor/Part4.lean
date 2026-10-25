/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.ContourAnchor.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Percolation (anchorFinset origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem sharedPrimalEdge_exitFaces (hfin : (cluster 2 ω (origin 2)).Finite) :
    sharedPrimalEdge (exitFaceUp (ω := ω) hfin) (exitFaceDown (ω := ω) hfin)
      = s(axisSite (exitIndex (ω := ω) hfin), axisSite (exitIndex (ω := ω) hfin + 1)) := by
  
  have hup : (exitFaceUp (ω := ω) hfin : Site 2)
      = ![(exitIndex (ω := ω) hfin : ℤ), 0] := rfl
  have hdown : (exitFaceDown (ω := ω) hfin : Site 2)
      = ![(exitIndex (ω := ω) hfin : ℤ), (0 : ℤ) - 1] := by
    unfold exitFaceDown; funext i; fin_cases i <;> simp
  have hax0 : (axisSite (exitIndex (ω := ω) hfin) : Site 2)
      = ![(exitIndex (ω := ω) hfin : ℤ), 0] := rfl
  have hax1 : (axisSite (exitIndex (ω := ω) hfin + 1) : Site 2)
      = ![(exitIndex (ω := ω) hfin : ℤ) + 1, 0] := by
    funext i; fin_cases i <;> simp [axisSite]
  rw [hup, hdown, sharedPrimalEdge_bottom (exitIndex (ω := ω) hfin : ℤ) 0,
    hax0, hax1]
  unfold faceCorner00 faceCorner10
  rfl


theorem exitFaces_adj (hfin : (cluster 2 ω (origin 2)).Finite) :
    (hypercubicLattice 2).Adj (exitFaceUp (ω := ω) hfin) (exitFaceDown (ω := ω) hfin) := by
  have hup : (exitFaceUp (ω := ω) hfin : Site 2)
      = ![(exitIndex (ω := ω) hfin : ℤ), 0] := rfl
  have hdown : (exitFaceDown (ω := ω) hfin : Site 2)
      = ![(exitIndex (ω := ω) hfin : ℤ), (0 : ℤ) - 1] := by
    unfold exitFaceDown; funext i; fin_cases i <;> simp
  rw [hup, hdown]
  exact latAdj_bottom (exitIndex (ω := ω) hfin : ℤ) 0


theorem exitFaces_faceBoundaryGraph_adj (hfin : (cluster 2 ω (origin 2)).Finite) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj
      (exitFaceUp (ω := ω) hfin) (exitFaceDown (ω := ω) hfin) := by
  rw [faceBoundaryGraph_adj]
  refine ⟨exitFaces_adj (ω := ω) hfin, ?_⟩
  rw [sharedPrimalEdge_exitFaces (ω := ω) hfin, bdEdge_mk]
  refine ⟨fun _ => axisSite_exit_succ_not_mem (ω := ω) hfin, fun _ => ?_⟩
  exact axisSite_exit_mem (ω := ω) hfin


theorem exitFaceUp_mem_anchorFinset (hfin : (cluster 2 ω (origin 2)).Finite) {m : ℕ}
    (hm : exitIndex (ω := ω) hfin < m) :
    exitFaceUp (ω := ω) hfin ∈ anchorFinset m := by
  classical
  unfold anchorFinset
  rw [Finset.mem_union]
  left
  rw [Finset.mem_image]
  exact ⟨exitIndex (ω := ω) hfin, Finset.mem_range.mpr hm, rfl⟩


theorem exitFaceDown_mem_anchorFinset (hfin : (cluster 2 ω (origin 2)).Finite) {m : ℕ}
    (hm : exitIndex (ω := ω) hfin < m) :
    exitFaceDown (ω := ω) hfin ∈ anchorFinset m := by
  classical
  unfold anchorFinset
  rw [Finset.mem_union]
  right
  rw [Finset.mem_image]
  exact ⟨exitIndex (ω := ω) hfin, Finset.mem_range.mpr hm, rfl⟩


theorem exists_anchored_faceBoundary_edge (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ (j : ℕ) (f g : Site 2),
      (faceBoundaryGraph (cluster 2 ω (origin 2))).Adj f g ∧
      (∀ m : ℕ, j < m → f ∈ anchorFinset m ∧ g ∈ anchorFinset m) := by
  refine ⟨exitIndex (ω := ω) hfin, exitFaceUp (ω := ω) hfin, exitFaceDown (ω := ω) hfin,
    exitFaces_faceBoundaryGraph_adj (ω := ω) hfin, fun m hm =>
      ⟨exitFaceUp_mem_anchorFinset (ω := ω) hfin hm,
       exitFaceDown_mem_anchorFinset (ω := ω) hfin hm⟩⟩


theorem exists_cycle_through_exitEdge (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u),
      c.IsCycle ∧
        s(exitFaceUp (ω := ω) hfin, exitFaceDown (ω := ω) hfin) ∈ c.edges := by
  obtain ⟨T, hT⟩ :=
    exists_finset_support_faceBoundaryGraph (cluster 2 ω (origin 2)) hfin
  exact EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
    (faceBoundaryGraph (cluster 2 ω (origin 2))) T hT
    (degree_faceBoundaryGraph_even (cluster 2 ω (origin 2)))
    (exitFaces_faceBoundaryGraph_adj (ω := ω) hfin)


theorem exists_cycle_based_exitFaceUp (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
        (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin)),
      c.IsCycle := by
  classical
  obtain ⟨u, c, hcyc, hedge⟩ := exists_cycle_through_exitEdge (ω := ω) hfin
  
  have hsup : exitFaceUp (ω := ω) hfin ∈ c.support :=
    c.fst_mem_support_of_mem_edges hedge
  exact ⟨c.rotate (exitFaceUp (ω := ω) hfin) hsup, hcyc.rotate hsup⟩


end Lattice
end StatMech
