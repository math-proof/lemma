/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit.Part8
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_rca_mem_rightEdges {e : Sym2 (Site 2)}
    (he : e ∈ rlc_rca_rightEdges) :
    e ∈ rlc_pathEdges rlc_retainedChoiceAuditRight.1 := by
  rwa [rlc_retainedChoiceAudit_right_edges]

theorem rlc_rca_mem_leftEdges {e : Sym2 (Site 2)}
    (he : e ∈ rlc_rca_leftEdges) :
    e ∈ rlc_pathEdges rlc_retainedChoiceAuditLeft.1 := by
  rwa [rlc_retainedChoiceAudit_left_edges]

theorem rlc_rca_mem_reflectedLeftEdges {x y : Site 2}
    (he : s(x, y) ∈ rlc_rca_leftEdges) :
    s(rlc_flipX x, rlc_flipX y) ∈
      rlc_reflectedPathEdges rlc_retainedChoiceAuditLeft.1 := by
  rw [rlc_reflectedPathEdges, Finset.mem_image]
  exact ⟨s(x, y), rlc_rca_mem_leftEdges he, by simp [Sym2.map_mk]⟩

theorem rlc_rca_regionWallEdges_subset_fourTrace :
    rlc_rca_regionWallEdges ⊆
      rlc_connectorFourTraceEdges
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
  intro e he
  simp only [rlc_rca_regionWallEdges, Finset.mem_insert,
    Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply rlc_rca_mem_leftEdges
    simp [rlc_rca_leftEdges]
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply rlc_rca_mem_leftEdges
    simp [rlc_rca_leftEdges]
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply rlc_rca_mem_rightEdges
    simp [rlc_rca_rightEdges]
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    simpa [rlc_flipX, rlc_flipXFun] using
      (rlc_rca_mem_reflectedLeftEdges (x := (![-2, 1] : Site 2))
        (y := ![-2, 2]) (by simp [rlc_rca_leftEdges]))
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply rlc_rca_mem_rightEdges
    simp [rlc_rca_rightEdges]
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply rlc_rca_mem_leftEdges
    simp [rlc_rca_leftEdges]
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply rlc_rca_mem_leftEdges
    simp [rlc_rca_leftEdges]
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    simpa [rlc_flipX, rlc_flipXFun] using
      (rlc_rca_mem_reflectedLeftEdges (x := (![-1, -2] : Site 2))
        (y := ![-1, -1]) (by simp [rlc_rca_leftEdges]))
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply rlc_rca_mem_leftEdges
    simp [rlc_rca_leftEdges]
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    simpa [rlc_flipX, rlc_flipXFun] using
      (rlc_rca_mem_reflectedLeftEdges (x := (![-1, -1] : Site 2))
        (y := ![-1, 0]) (by simp [rlc_rca_leftEdges]))

set_option maxHeartbeats 1000000 in
theorem rlc_rca_faceRegion_step {u v : Site 2}
    (hu : u ∈ rlc_rca_faceRegion)
    (huv : (hypercubicLattice 2).Adj u v)
    (hvBox : v ∈ rlc_connectorFaceBox 2)
    (hnotWall : sharedPrimalEdge u v ∉
      rlc_connectorFourTraceEdges
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft) :
    v ∈ rlc_rca_faceRegion := by
  have hvCand := mem_candFinset_of_adj 2 u v huv
  simp only [rlc_rca_faceRegion, Finset.mem_insert,
    Finset.mem_singleton] at hu
  have hdich : v ∈ rlc_rca_faceRegion ∨
      sharedPrimalEdge u v ∈ rlc_rca_regionWallEdges ∨
      v ∉ rlc_connectorFaceBox 2 := by
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [candFinset_face] at hvCand <;>
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand <;>
      rcases hvCand with rfl | rfl | rfl | rfl <;>
      simp [rlc_rca_faceRegion, rlc_connectorFaceBox, mem_rect,
        sharedPrimalEdge, rlc_rca_regionWallEdges]
  rcases hdich with hv | hwall | hvOut
  · exact hv
  · exact False.elim
      (hnotWall (rlc_rca_regionWallEdges_subset_fourTrace hwall))
  · exact False.elim (hvOut hvBox)

theorem rlc_rca_centralFaceRegion_subset {z : Site 2}
    (hz : z ∈ rlc_connectorCentralFaceRegion
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft) :
    z ∈ rlc_rca_faceRegion := by
  have hzSet : z ∈ rlc_connectorCentralFaceRegionSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
    simpa [rlc_connectorCentralFaceRegion] using hz
  obtain ⟨hzBox, hsBox, hzReach⟩ := hzSet
  obtain ⟨p⟩ := hzReach
  have hstart : rlc_connectorCentralFace ∈ rlc_rca_faceRegion := by
    simp [rlc_connectorCentralFace, rlc_rca_faceRegion]
  have walk_stays {x y : RlcConnectorFaceVertex 2}
      (q : (rlc_connectorFiniteFaceCutGraph
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft).Walk x y)
      (hx : (x : Site 2) ∈ rlc_rca_faceRegion) :
      (y : Site 2) ∈ rlc_rca_faceRegion := by
    induction q with
    | nil => exact hx
    | @cons a b c hab q ih =>
        have hab' := hab
        change ((rlc_connectorFourTraceFaceCutGraph
          rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft).induce
            (rlc_connectorFaceBox 2 : Set (Site 2))).Adj a b at hab'
        rw [SimpleGraph.induce_adj,
          rlc_connectorFourTraceFaceCutGraph_adj] at hab'
        exact ih (rlc_rca_faceRegion_step hx hab'.1 b.2 hab'.2)
  exact walk_stays p hstart

theorem rlc_rca_top_exit_not_wall :
    s((![-2, 2] : Site 2), ![-3, 2]) ∉
      rlc_connectorFourTraceEdges
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
  intro hwall
  rw [rlc_connectorFourTraceEdges, Finset.mem_union,
    rlc_connectorReflectedTraceEdges, Finset.mem_union] at hwall
  rcases hwall with horiginal | hreflected
  · rcases horiginal with hright | hleft
    · have hright' : s((![-2, 2] : Site 2), ![-3, 2]) ∈
          rlc_rca_rightEdges := by
        rw [← rlc_retainedChoiceAudit_right_edges]
        exact hright
      simpa [rlc_rca_rightEdges, Sym2.eq_iff] using hright'
    · have hleft' : s((![-2, 2] : Site 2), ![-3, 2]) ∈
          rlc_rca_leftEdges := by
        rw [← rlc_retainedChoiceAudit_left_edges]
        exact hleft
      simpa [rlc_rca_leftEdges, Sym2.eq_iff] using hleft'
  · rw [Finset.mem_union] at hreflected
    rcases hreflected with hflipRight | hflipLeft
    · have he := rlc_mem_pathEdges_of_reflected_mk
        rlc_retainedChoiceAuditRight.1
        (x := (![2, 2] : Site 2)) (y := ![3, 2]) (by
          simpa [rlc_flipX, rlc_flipXFun] using hflipRight)
      have he' : s((![2, 2] : Site 2), ![3, 2]) ∈
          rlc_rca_rightEdges := by
        rw [← rlc_retainedChoiceAudit_right_edges]
        exact he
      simpa [rlc_rca_rightEdges, Sym2.eq_iff] using he'
    · have he := rlc_mem_pathEdges_of_reflected_mk
        rlc_retainedChoiceAuditLeft.1
        (x := (![2, 2] : Site 2)) (y := ![3, 2]) (by
          simpa [rlc_flipX, rlc_flipXFun] using hflipLeft)
      have he' : s((![2, 2] : Site 2), ![3, 2]) ∈
          rlc_rca_leftEdges := by
        rw [← rlc_retainedChoiceAudit_left_edges]
        exact he
      simpa [rlc_rca_leftEdges, Sym2.eq_iff] using he'

theorem rlc_rca_bottom_exit_not_wall :
    s((![-2, -1] : Site 2), ![-1, -1]) ∉
      rlc_connectorFourTraceEdges
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
  intro hwall
  rw [rlc_connectorFourTraceEdges, Finset.mem_union,
    rlc_connectorReflectedTraceEdges, Finset.mem_union] at hwall
  rcases hwall with horiginal | hreflected
  · rcases horiginal with hright | hleft
    · have hright' : s((![-2, -1] : Site 2), ![-1, -1]) ∈
          rlc_rca_rightEdges := by
        rw [← rlc_retainedChoiceAudit_right_edges]
        exact hright
      simpa [rlc_rca_rightEdges, Sym2.eq_iff] using hright'
    · have hleft' : s((![-2, -1] : Site 2), ![-1, -1]) ∈
          rlc_rca_leftEdges := by
        rw [← rlc_retainedChoiceAudit_left_edges]
        exact hleft
      simpa [rlc_rca_leftEdges, Sym2.eq_iff] using hleft'
  · rw [Finset.mem_union] at hreflected
    rcases hreflected with hflipRight | hflipLeft
    · have he := rlc_mem_pathEdges_of_reflected_mk
        rlc_retainedChoiceAuditRight.1
        (x := (![2, -1] : Site 2)) (y := ![1, -1]) (by
          simpa [rlc_flipX, rlc_flipXFun] using hflipRight)
      have he' : s((![2, -1] : Site 2), ![1, -1]) ∈
          rlc_rca_rightEdges := by
        rw [← rlc_retainedChoiceAudit_right_edges]
        exact he
      simpa [rlc_rca_rightEdges, Sym2.eq_iff] using he'
    · have he := rlc_mem_pathEdges_of_reflected_mk
        rlc_retainedChoiceAuditLeft.1
        (x := (![2, -1] : Site 2)) (y := ![1, -1]) (by
          simpa [rlc_flipX, rlc_flipXFun] using hflipLeft)
      have he' : s((![2, -1] : Site 2), ![1, -1]) ∈
          rlc_rca_leftEdges := by
        rw [← rlc_retainedChoiceAudit_left_edges]
        exact he
      simpa [rlc_rca_leftEdges, Sym2.eq_iff] using he'

theorem rlc_rca_top_exit_not_carrier :
    ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        (![1, 1] : Site 2) ![2, 1] := by
  rw [rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft (by simp)]
  rw [rlc_mem_connectorCentralFacePlanarEdges_iff
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft (by simp)]
  rintro (hwall | ⟨_hx, _hy, f, hf, hflank⟩)
  · exact rlc_rca_top_exit_not_wall hwall
  · have hf' := rlc_rca_centralFaceRegion_subset hf
    simp [rlc_rca_faceRegion, flankFaces, rlc_dualReflect,
      rlc_dualReflectFun] at hf' hflank
    rcases hflank with hflank | hflank <;> subst f <;> simp at hf'

theorem rlc_rca_bottom_exit_not_carrier :
    ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        (![1, -2] : Site 2) ![0, -2] := by
  rw [rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft (by simp)]
  rw [rlc_mem_connectorCentralFacePlanarEdges_iff
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft (by simp)]
  rintro (hwall | ⟨_hx, _hy, f, hf, hflank⟩)
  · exact rlc_rca_bottom_exit_not_wall hwall
  · have hf' := rlc_rca_centralFaceRegion_subset hf
    simp [rlc_rca_faceRegion, flankFaces, rlc_dualReflect,
      rlc_dualReflectFun] at hf' hflank
    rcases hflank with hflank | hflank <;> subst f <;> simp at hf'

theorem rlc_rca_rightVertex_mem_filled {z : Site 2}
    (hz : z ∈ rlc_pathVertices rlc_retainedChoiceAuditRight.1) :
    z ∈ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig :=
  rlc_connectorCentralFaceReachSet_subset_filled _ _ _
    (rlc_rightPathVertex_mem_centralFaceReachSet _ _ _ hz)

theorem rlc_rca_leftVertex_not_mem_filled {z : Site 2}
    (hz : z ∈ rlc_pathVertices rlc_retainedChoiceAuditLeft.1) :
    z ∉ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  have hzExt := rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAudit_faithful.toRlcBookPositionedTracePair
      rlc_retainedChoiceAuditConfig rlc_retainedChoiceAudit_source_failure hz
  simpa [rlc_connectorCentralFaceFilledReachSet] using hzExt

theorem rlc_rca_exterior_of_adj_exterior {z w : Site 2}
    (hzNot : z ∉ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig)
    (hwExt : w ∈ rlc_connectorCentralFaceExteriorSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig)
    (hzw : (hypercubicLattice 2).Adj z w) :
    z ∈ rlc_connectorCentralFaceExteriorSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  refine ⟨hzNot, ?_⟩
  have hreach : ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig)ᶜ).Reachable
      ⟨z, hzNot⟩ ⟨w, hwExt.1⟩ := by
    exact (show ((hypercubicLattice 2).induce
      (rlc_connectorCentralFaceReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig)ᶜ).Adj
          ⟨z, hzNot⟩ ⟨w, hwExt.1⟩ from hzw).reachable
  exact (ConnectedComponent.sound hreach).trans hwExt.2

theorem rlc_rca_zero_one_not_mem_filled :
    (![0, 1] : Site 2) ∉ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  have hzNot : (![0, 1] : Site 2) ∉ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := fun hz => by
    have := rlc_rca_reachSet_subset_sourceSet hz
    simpa [rlc_rca_sourceSet] using this
  have hwLeft : (![-1, 1] : Site 2) ∈
      rlc_pathVertices rlc_retainedChoiceAuditLeft.1 := by
    rw [rlc_retainedChoiceAudit_left_vertices]
    simp
  have hwExt := rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAudit_faithful.toRlcBookPositionedTracePair
      rlc_retainedChoiceAuditConfig rlc_retainedChoiceAudit_source_failure hwLeft
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hzNot hwExt (by simp))

theorem rlc_rca_zero_neg_one_not_mem_filled :
    (![0, -1] : Site 2) ∉ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  have hzNot : (![0, -1] : Site 2) ∉ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := fun hz => by
    have := rlc_rca_reachSet_subset_sourceSet hz
    simpa [rlc_rca_sourceSet] using this
  have hwLeft : (![-1, -1] : Site 2) ∈
      rlc_pathVertices rlc_retainedChoiceAuditLeft.1 := by
    rw [rlc_retainedChoiceAudit_left_vertices]
    simp
  have hwExt := rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAudit_faithful.toRlcBookPositionedTracePair
      rlc_retainedChoiceAuditConfig rlc_retainedChoiceAudit_source_failure hwLeft
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hzNot hwExt (by simp))

theorem rlc_rca_one_neg_one_not_mem_filled :
    (![1, -1] : Site 2) ∉ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  have hzNot : (![1, -1] : Site 2) ∉ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := fun hz => by
    have := rlc_rca_reachSet_subset_sourceSet hz
    simpa [rlc_rca_sourceSet] using this
  have hwExt : (![0, -1] : Site 2) ∈
      rlc_connectorCentralFaceExteriorSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig := by
    simpa [rlc_connectorCentralFaceFilledReachSet] using
      rlc_rca_zero_neg_one_not_mem_filled
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hzNot hwExt (by simp))

theorem rlc_rca_one_two_not_mem_filled :
    (![1, 2] : Site 2) ∉ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  have hzNot : (![1, 2] : Site 2) ∉ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := fun hz => by
    have := rlc_rca_reachSet_subset_sourceSet hz
    simpa [rlc_rca_sourceSet] using this
  have hwLeft : (![0, 2] : Site 2) ∈
      rlc_pathVertices rlc_retainedChoiceAuditLeft.1 := by
    rw [rlc_retainedChoiceAudit_left_vertices]
    simp
  have hwExt := rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAudit_faithful.toRlcBookPositionedTracePair
      rlc_retainedChoiceAuditConfig rlc_retainedChoiceAudit_source_failure hwLeft
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hzNot hwExt (by simp))

theorem rlc_rca_two_two_not_mem_filled :
    (![2, 2] : Site 2) ∉ rlc_connectorCentralFaceFilledReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := by
  have hzNot : (![2, 2] : Site 2) ∉ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := fun hz => by
    have := rlc_rca_reachSet_subset_sourceSet hz
    simpa [rlc_rca_sourceSet] using this
  have hwExt : (![1, 2] : Site 2) ∈
      rlc_connectorCentralFaceExteriorSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig := by
    simpa [rlc_connectorCentralFaceFilledReachSet] using
      rlc_rca_one_two_not_mem_filled
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hzNot hwExt (by simp))

end
end StatMech.Universality
