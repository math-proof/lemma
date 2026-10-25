/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.atsattachsurgery.Part4
import Theorem.StatisticalMechanics.Code.Walls.arrreroute.Part5
import Def.StatisticalMechanics.Code.Walls.cycboundary.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem cyc_pinch_face_degree_four :
    (faceBoundaryGraph (↑cyc_pinch : Set (Site 2))).degree ![(0:ℤ), 0] = 4 := by
  rw [show (![(0:ℤ), 0] : Site 2) = ![(0:ℤ), (0:ℤ)] from rfl, degree_faceBoundaryGraph]
  unfold faceBoundaryDegree bdInd faceCorner00 faceCorner10 faceCorner11 faceCorner01 cyc_pinch
  have h00 : (![(0:ℤ), 0] : Site 2) ∈ (↑({![(0:ℤ), 0], ![(1:ℤ), 1]} : Finset (Site 2))
      : Set (Site 2)) := by simp
  have h11 : (![(1:ℤ), 1] : Site 2) ∈ (↑({![(0:ℤ), 0], ![(1:ℤ), 1]} : Finset (Site 2))
      : Set (Site 2)) := by simp
  have h10 : (![(1:ℤ), 0] : Site 2) ∉ (↑({![(0:ℤ), 0], ![(1:ℤ), 1]} : Finset (Site 2))
      : Set (Site 2)) := by
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [site2_eq, site2_eq]; omega
  have h01 : (![(0:ℤ), 1] : Site 2) ∉ (↑({![(0:ℤ), 0], ![(1:ℤ), 1]} : Finset (Site 2))
      : Set (Site 2)) := by
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [site2_eq, site2_eq]; omega
  simp only [show ((0:ℤ) + 1) = 1 from by ring]
  rw [if_pos (by tauto), if_pos (by tauto), if_pos (by tauto), if_pos (by tauto)]


theorem cyc_pinch_not_boundaryCycle :
    ¬ cyc_BoundaryCycle (↑cyc_pinch : Set (Site 2)) := by
  intro h
  
  have hd4 := cyc_pinch_face_degree_four
  have hsupp : (![(0:ℤ), 0] : Site 2) ∈ (faceBoundaryGraph (↑cyc_pinch : Set (Site 2))).support := by
    have hpos : 0 < (faceBoundaryGraph (↑cyc_pinch : Set (Site 2))).degree ![(0:ℤ), 0] := by
      rw [hd4]; norm_num
    obtain ⟨g, hg⟩ := SimpleGraph.degree_pos_iff_nonempty.mp hpos
    exact ⟨g, hg⟩
  have hd2 := cyc_degreeTwo h hsupp
  rw [hd4] at hd2
  norm_num at hd2


theorem cyc_mem_support_iff_neighbor_nonempty {K : Set (Site 2)} {f : Site 2} :
    f ∈ (faceBoundaryGraph K).support ↔ ((faceBoundaryGraph K).neighborSet f).Nonempty := by
  constructor
  · rintro ⟨g, hg⟩; exact ⟨g, hg⟩
  · rintro ⟨g, hg⟩; exact ⟨g, hg⟩


theorem cyc_neighborSet_ncard_of_degree_two {K : Set (Site 2)} {f : Site 2}
    (h : (faceBoundaryGraph K).degree f = 2) :
    ((faceBoundaryGraph K).neighborSet f).ncard = 2 := by
  classical
  have hbridge : ((faceBoundaryGraph K).neighborSet f).ncard
      = (faceBoundaryGraph K).degree f := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
  rw [hbridge, h]


theorem cyc_isCycles_of_boundaryCycle {K : Set (Site 2)} (h : cyc_BoundaryCycle K) :
    (faceBoundaryGraph K).IsCycles := by
  intro v hv
  have hsupp : v ∈ (faceBoundaryGraph K).support :=
    cyc_mem_support_iff_neighbor_nonempty.mpr hv
  exact cyc_neighborSet_ncard_of_degree_two (cyc_degreeTwo h hsupp)


theorem cyc_degree_two_of_isCycles {K : Set (Site 2)} (h : (faceBoundaryGraph K).IsCycles)
    {f : Site 2} (hf : f ∈ (faceBoundaryGraph K).support) :
    (faceBoundaryGraph K).degree f = 2 := by
  classical
  have hne := cyc_mem_support_iff_neighbor_nonempty.mp hf
  have hnc : ((faceBoundaryGraph K).neighborSet f).ncard = 2 := h hne
  have hbridge : ((faceBoundaryGraph K).neighborSet f).ncard
      = (faceBoundaryGraph K).degree f := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
  rw [← hbridge, hnc]


theorem cyc_boundaryCycle_of_isCycles {K : Set (Site 2)}
    (hreach : fbc_BoundaryReachable K) (hcyc : (faceBoundaryGraph K).IsCycles) :
    cyc_BoundaryCycle K :=
  ⟨hreach, fun _f hf => cyc_degree_two_of_isCycles hcyc hf⟩


theorem cyc_reachable_deleteEdge {K : Finset (Site 2)} {v w : Site 2}
    (hadj : (faceBoundaryGraph (↑K : Set (Site 2))).Adj v w) :
    ((faceBoundaryGraph (↑K : Set (Site 2))).deleteEdges {s(v, w)}).Reachable v w := by
  classical
  set G := faceBoundaryGraph (↑K : Set (Site 2)) with hG
  
  obtain ⟨T, hsupp⟩ :=
    exists_finset_support_faceBoundaryGraph (↑K : Set (Site 2)) (K : Set (Site 2)).toFinite
  rw [← hG] at hsupp
  set H := G.induce (T : Set (Site 2)) with hH
  haveI : Fintype (T : Set (Site 2)) := FinsetCoe.fintype T
  haveI : DecidableRel H.Adj := Classical.decRel _
  have hvT : v ∈ (T : Set (Site 2)) := hsupp hadj.mem_support_left
  have hwT : w ∈ (T : Set (Site 2)) := hsupp hadj.mem_support_right
  
  have hdegH : ∀ x : (T : Set (Site 2)), H.degree x = G.degree (x : Site 2) := by
    intro x
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    refine Fintype.card_congr ?_
    refine ⟨fun y => ⟨(y.1 : Site 2), y.2⟩,
      fun y => ⟨⟨y.1, hsupp y.2.symm.mem_support_left⟩, y.2⟩, ?_, ?_⟩
    · intro y; ext; rfl
    · intro y; ext; rfl
  have hHeven : ∀ x : (T : Set (Site 2)), Even (H.degree x) := by
    intro x; rw [hdegH x]; exact degree_faceBoundaryGraph_even _ _
  have hadjH : H.Adj ⟨v, hvT⟩ ⟨w, hwT⟩ := hadj
  
  have hrH := EvenDegree.reachable_deleteEdges_of_even H hHeven hadjH
  
  obtain ⟨p⟩ := hrH
  let emb : H ↪g G := SimpleGraph.Embedding.induce (T : Set (Site 2))
  
  let φ : (H.deleteEdges {s((⟨v, hvT⟩ : (T : Set (Site 2))), ⟨w, hwT⟩)})
      →g (G.deleteEdges {s(v, w)}) := by
    refine ⟨fun x => (x : Site 2), ?_⟩
    intro a b hab
    rw [SimpleGraph.deleteEdges_adj] at hab ⊢
    refine ⟨emb.toHom.map_adj hab.1, ?_⟩
    intro hmem
    apply hab.2
    rw [Set.mem_singleton_iff] at hmem ⊢
    rw [Sym2.eq_iff] at hmem ⊢
    rcases hmem with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · left; exact ⟨Subtype.ext ha, Subtype.ext hb⟩
    · right; exact ⟨Subtype.ext ha, Subtype.ext hb⟩
  exact ⟨p.map φ⟩


end Walls
end StatMech
