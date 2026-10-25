/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit.Part9
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

set_option maxHeartbeats 1000000 in
theorem rlc_rca_upperGoodComponent_step {u v : Site 2}
    (hu : u ∈ rlc_rca_upperGoodComponent)
    (huv : (rlc_connectorCentralFaceGoodBoundaryGraph
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig).Adj u v) :
    v ∈ rlc_rca_upperGoodComponent := by
  have h02Out : (![0, 2] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_leftVertex_not_mem_filled (by
      rw [rlc_retainedChoiceAudit_left_vertices]
      simp)
  have hm1m1Out : (![-1, -1] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_leftVertex_not_mem_filled (by
      rw [rlc_retainedChoiceAudit_left_vertices]
      simp)
  have hm10Out : (![-1, 0] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_leftVertex_not_mem_filled (by
      rw [rlc_retainedChoiceAudit_left_vertices]
      simp)
  have hm11Out : (![-1, 1] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_leftVertex_not_mem_filled (by
      rw [rlc_retainedChoiceAudit_left_vertices]
      simp)
  have h10In : (![1, 0] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have h11In : (![1, 1] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have h21In : (![2, 1] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have h2m1In : (![2, -1] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have h20In : (![2, 0] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have h2m2In : (![2, -2] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have h1m2In : (![1, -2] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig :=
    rlc_rca_rightVertex_mem_filled (by
      rw [rlc_retainedChoiceAudit_right_vertices]
      simp)
  have hvCand := mem_candFinset_of_adj 2 u v huv.1.1
  simp only [rlc_rca_upperGoodComponent, Finset.mem_insert,
    Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [candFinset_face] at hvCand <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand <;>
    rcases hvCand with rfl | rfl | rfl | rfl
  all_goals try simp [rlc_rca_upperGoodComponent]
  all_goals try exact False.elim (rlc_rca_top_exit_not_carrier huv.2)
  all_goals try exact False.elim (rlc_rca_bottom_exit_not_carrier huv.2)
  all_goals
    exfalso
    have hbd := huv.1.2
    simp [sharedPrimalEdge, bdEdge_mk,
      rlc_rca_zero_one_not_mem_filled,
      rlc_rca_zero_neg_one_not_mem_filled,
      rlc_rca_one_neg_one_not_mem_filled,
      rlc_rca_one_two_not_mem_filled,
      rlc_rca_two_two_not_mem_filled,
      h02Out, hm1m1Out, hm10Out, hm11Out,
      h10In, h11In, h21In, h2m1In, h20In, h2m2In, h1m2In] at hbd


theorem rlc_retainedChoiceAudit_upperComponent_no_right_contact
    {z : Site 2}
    (hz : (rlc_connectorCentralFaceGoodBoundaryGraph
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig).Reachable (![-1, 0] : Site 2) z) :
    rlc_dualReflect z ∉
      rlc_pathVertices rlc_retainedChoiceAuditRight.1 := by
  obtain ⟨p⟩ := hz
  have hstart : (![-1, 0] : Site 2) ∈ rlc_rca_upperGoodComponent := by
    simp [rlc_rca_upperGoodComponent]
  have hzComponent : z ∈ rlc_rca_upperGoodComponent := by
    have walk_stays {a b : Site 2}
        (q : (rlc_connectorCentralFaceGoodBoundaryGraph
          rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
          rlc_retainedChoiceAuditConfig).Walk a b)
        (ha : a ∈ rlc_rca_upperGoodComponent) :
        b ∈ rlc_rca_upperGoodComponent := by
      induction q with
      | nil => exact ha
      | @cons c d e hcd q ih =>
          exact ih (rlc_rca_upperGoodComponent_step ha hcd)
    exact walk_stays p hstart
  rw [rlc_retainedChoiceAudit_right_vertices]
  simp only [rlc_rca_upperGoodComponent, Finset.mem_insert,
    Finset.mem_singleton] at hzComponent
  rcases hzComponent with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rlc_dualReflect, rlc_dualReflectFun]


theorem rlc_retainedChoiceAudit_topWall_endpoint_not_mem_filled :
    (![-3, 2] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig := by
  have hpNotReach : (![-3, 2] : Site 2) ∉
      rlc_connectorCentralFaceReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig := fun hp => by
    have hp' := rlc_rca_reachSet_subset_sourceSet hp
    simpa [rlc_rca_sourceSet] using hp'
  have hqLeft : (![-2, 2] : Site 2) ∈
      rlc_pathVertices rlc_retainedChoiceAuditLeft.1 := by
    rw [rlc_retainedChoiceAudit_left_vertices]
    simp
  have hqExterior :=
    rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAudit_faithful.toRlcBookPositionedTracePair
      rlc_retainedChoiceAuditConfig rlc_retainedChoiceAudit_source_failure
      hqLeft
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hpNotReach hqExterior (by simp))


theorem rlc_retainedChoiceAudit_reflectedRight_endpoint_not_mem_filled :
    (![-2, -1] : Site 2) ∉
      rlc_connectorCentralFaceFilledReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig := by
  have hpNotReach : (![-2, -1] : Site 2) ∉
      rlc_connectorCentralFaceReachSet
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
        rlc_retainedChoiceAuditConfig := fun hp => by
    have hp' := rlc_rca_reachSet_subset_sourceSet hp
    simpa [rlc_rca_sourceSet] using hp'
  have hqLeft : (![-1, -1] : Site 2) ∈
      rlc_pathVertices rlc_retainedChoiceAuditLeft.1 := by
    rw [rlc_retainedChoiceAudit_left_vertices]
    simp
  have hqExterior :=
    rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAudit_faithful.toRlcBookPositionedTracePair
      rlc_retainedChoiceAuditConfig rlc_retainedChoiceAudit_source_failure
      hqLeft
  simpa [rlc_connectorCentralFaceFilledReachSet] using
    (rlc_rca_exterior_of_adj_exterior hpNotReach hqExterior (by simp))

end
end StatMech.Universality
