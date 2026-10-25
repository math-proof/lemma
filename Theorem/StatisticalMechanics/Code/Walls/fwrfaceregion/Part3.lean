/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Theorem.StatisticalMechanics.Code.Walls.ceosimplecycle
import Theorem.StatisticalMechanics.Code.Walls.dowdartwinding
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
import Def.StatisticalMechanics.Code.Walls.fwrfaceregion.Part2
open Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem fwr_primalWalkBoundsFaceRegion : fwr_PrimalWalkBoundsFaceRegion := by
  intro a Vc hnd u v huv
  exact fwr_primalWalkBoundsFaceRegion_of_nodup Vc hnd huv


theorem fwr_shiftSquare_faces_adj :
    (hypercubicLattice 2).Adj (![0, 0] : Site 2) (![0, 1] : Site 2) := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]


theorem fwr_shiftSquare_shared :
    sharedPrimalEdge (![0, 0] : Site 2) (![0, 1] : Site 2)
      = s((![0, 1] : Site 2), (![1, 1] : Site 2)) := by
  rw [show (![0, 1] : Site 2) = ![(0 : ℤ), 0 + 1] by norm_num, sharedPrimalEdge_top]
  unfold faceCorner01 faceCorner11; norm_num


theorem fwr_shiftSquare_faceCut_works :
    (fwr_faceInside ceo_shiftSquare (![0, 0] : Site 2)
      ↔ ¬ fwr_faceInside ceo_shiftSquare (![0, 1] : Site 2)) := by
  have hd : (fwr_faceInside ceo_shiftSquare (![0, 0] : Site 2)
      ↔ ¬ fwr_faceInside ceo_shiftSquare (![0, 1] : Site 2))
      ↔ sharedPrimalEdge (![0, 0] : Site 2) (![0, 1] : Site 2) ∈ ceo_shiftSquare.edges :=
    fwr_faceCutMatch_of_nodup ceo_shiftSquare ceo_shiftSquare_edges_nodup fwr_shiftSquare_faces_adj
  rw [hd, fwr_shiftSquare_shared]
  exact ceo_shiftSquare_edge_mem


theorem fwr_shiftSquare_rayCounts :
    jec_rayCount (![1, 1] : Site 2) ceo_shiftSquare = 0
      ∧ jec_rayCount (![1, 2] : Site 2) ceo_shiftSquare = 1 :=
  ⟨(ceo_shiftSquare_rayCount_endpoints).2, ceo_shiftSquare_inside_odd⟩


theorem fwr_shiftSquare_nonedge_left :
    s((![0, 0] : Site 2), (![0, 1] : Site 2)) ∉ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]

theorem fwr_shiftSquare_nonedge_bottom :
    s((![0, 0] : Site 2), (![1, 0] : Site 2)) ∉ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]

theorem fwr_shiftSquare_nonedge_right :
    s((![1, 0] : Site 2), (![1, 1] : Site 2)) ∉ ceo_shiftSquare.edges := by
  unfold ceo_shiftSquare
  simp [SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]


theorem fwr_primalWalkBoundsRegion_false : ¬ PrimalWalkBoundsRegion := by
  intro h
  obtain ⟨S, hS⟩ := h ceo_shiftSquare
  have hadj_ab : (hypercubicLattice 2).Adj (![0, 1] : Site 2) (![1, 1] : Site 2) := ceo_uv_adj
  have hadj_a0 : (hypercubicLattice 2).Adj (![0, 0] : Site 2) (![0, 1] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hadj_01 : (hypercubicLattice 2).Adj (![0, 0] : Site 2) (![1, 0] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hadj_1b : (hypercubicLattice 2).Adj (![1, 0] : Site 2) (![1, 1] : Site 2) := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  
  have hab : bdEdge S s((![0, 1] : Site 2), (![1, 1] : Site 2)) :=
    (hS hadj_ab).mp (List.mem_toFinset.mpr ceo_shiftSquare_edge_mem)
  
  have ha0 : ¬ bdEdge S s((![0, 0] : Site 2), (![0, 1] : Site 2)) := fun hbd =>
    fwr_shiftSquare_nonedge_left (List.mem_toFinset.mp ((hS hadj_a0).mpr hbd))
  have h01 : ¬ bdEdge S s((![0, 0] : Site 2), (![1, 0] : Site 2)) := fun hbd =>
    fwr_shiftSquare_nonedge_bottom (List.mem_toFinset.mp ((hS hadj_01).mpr hbd))
  have h1b : ¬ bdEdge S s((![1, 0] : Site 2), (![1, 1] : Site 2)) := fun hbd =>
    fwr_shiftSquare_nonedge_right (List.mem_toFinset.mp ((hS hadj_1b).mpr hbd))
  rw [bdEdge_mk] at hab ha0 h01 h1b
  
  by_cases m01 : (![0, 1] : Site 2) ∈ S <;> by_cases m11 : (![1, 1] : Site 2) ∈ S <;>
    by_cases m00 : (![0, 0] : Site 2) ∈ S <;> by_cases m10 : (![1, 0] : Site 2) ∈ S <;>
    simp_all


theorem fwr_faceCutMatch_nil {a : Site 2} {c d : Site 2}
    (hcd : (hypercubicLattice 2).Adj c d) :
    (fwr_faceInside (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a) c
      ↔ ¬ fwr_faceInside (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a) d)
      ↔ sharedPrimalEdge c d ∈ (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a).edges :=
  fwr_faceCutMatch_of_nodup _ (by simp) hcd


theorem fwr_scope {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {c d : Site 2} (hcd : (hypercubicLattice 2).Adj c d) :
    ((fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d)
      ↔ Odd (Vc.edges.count (sharedPrimalEdge c d)))
    ∧ (Vc.edges.Nodup →
      ((fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d) ↔ sharedPrimalEdge c d ∈ Vc.edges)) :=
  ⟨fwr_faceCutFlip Vc hcd, fun hnd => fwr_faceCutMatch_of_nodup Vc hnd hcd⟩

end Walls
end StatMech
