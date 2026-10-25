/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceRetainedChoiceAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceRetainedChoiceAudit.Part7
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_rca_right_subset_sourceSet {z : Site 2}
    (hz : z ∈ rlc_pathVertices rlc_retainedChoiceAuditRight.1) :
    z ∈ rlc_rca_sourceSet := by
  rw [rlc_retainedChoiceAudit_right_vertices] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rlc_rca_sourceSet]

theorem rlc_rca_sourceSet_disjoint_left {z : Site 2}
    (hz : z ∈ rlc_rca_sourceSet)
    (hzLeft : z ∈ rlc_pathVertices rlc_retainedChoiceAuditLeft.1) : False := by
  rw [rlc_retainedChoiceAudit_left_vertices] at hzLeft
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzLeft
  rcases hzLeft with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [rlc_rca_sourceSet] at hz

theorem rlc_rca_ambient_open_step {u v : Site 2}
    (hu : u ∈ rlc_rca_sourceSet)
    (hvBox : v ∈ rect (-4) 4 (-2) 2)
    (hopen : rlc_connectorCentralFaceAmbientConfig
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig s(u, v) = true) :
    v ∈ rlc_rca_sourceSet := by
  let e : Sym2 (Site 2) := s(u, v)
  by_cases hcarrier : e ∈ rlc_connectorCentralFaceEdges
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
  · have hopen' : rlc_retainedChoiceAuditConfig
        (rlc_connectorCentralFaceEdgeLift e hcarrier) = true := by
      change rlc_connectorCentralFaceAmbientConfig
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
          rlc_retainedChoiceAuditConfig e = true at hopen
      rw [rlc_connectorCentralFaceAmbientConfig_support
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
          rlc_retainedChoiceAuditConfig hcarrier] at hopen
      exact hopen
    have heOpen : e ∈ rlc_retainedChoiceAuditOpenEdges := by
      have := (rlc_retainedChoiceAuditConfig_eq_true_iff
        (rlc_connectorCentralFaceEdgeLift e hcarrier)).1 hopen'
      rwa [rlc_connectorCentralFaceEdgeLift_map] at this
    simp only [rlc_retainedChoiceAuditOpenEdges, Finset.mem_insert,
      Finset.mem_singleton] at heOpen
    rcases heOpen with he | he | he | he <;>
      rw [Sym2.eq_iff] at he <;>
      rcases he with ⟨huv, hvu⟩ | ⟨huv, hvu⟩ <;>
      subst u <;> subst v <;>
      simp [rlc_rca_sourceSet, mem_rect] at hu hvBox ⊢
  · have horiginal : e ∈
        rlc_pathEdges rlc_retainedChoiceAuditRight.1 ∪
          rlc_pathEdges rlc_retainedChoiceAuditLeft.1 := by
      simpa [rlc_connectorCentralFaceAmbientConfig, e, hcarrier] using hopen
    rw [Finset.mem_union] at horiginal
    rcases horiginal with hright | hleft
    · exact rlc_rca_right_subset_sourceSet
        (rlc_pathEdge_endpoints_mem_vertices
          rlc_retainedChoiceAuditRight.1 hright).2
    · exact False.elim (rlc_rca_sourceSet_disjoint_left hu
        (rlc_pathEdge_endpoints_mem_vertices
          rlc_retainedChoiceAuditLeft.1 hleft).1)

theorem rlc_rca_reachSet_subset_sourceSet {z : Site 2}
    (hz : z ∈ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig) : z ∈ rlc_rca_sourceSet := by
  obtain ⟨_hzBox, hzReach⟩ := hz
  obtain ⟨p⟩ := hzReach
  have hstart : ((rlc_connectorRightAnchor
      rlc_retainedChoiceAuditRight : RlcConnectorVertex 2) : Site 2) ∈
      rlc_rca_sourceSet := by
    simp [rlc_connectorRightAnchor, rlc_retainedChoiceAuditRight,
      rlc_rca_rv, rlc_rca_sourceSet]
  have walk_stays {x y : rect (-4) 4 (-2) 2}
      (q : (openSubgraphInduce 2
        (rlc_connectorCentralFaceAmbientConfig
          rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
          rlc_retainedChoiceAuditConfig)
        (rect (-4) 4 (-2) 2)).Walk x y)
      (hx : (x : Site 2) ∈ rlc_rca_sourceSet) :
      (y : Site 2) ∈ rlc_rca_sourceSet := by
    induction q with
    | nil => exact hx
    | @cons a b c hab q ih =>
        rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
        exact ih (rlc_rca_ambient_open_step hx b.2 hab.2)
  exact walk_stays p hstart


theorem rlc_retainedChoiceAudit_source_failure :
    rlc_retainedChoiceAuditConfig ∉
      rlc_finiteCentralFaceRandomConnectorEvent
        rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft := by
  rintro ⟨x, y, hx, hy, hxy⟩
  have hright := rlc_connectorTraceWiring_reachable_right
    rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      (rlc_connectorRightAnchor_onRight rlc_retainedChoiceAuditRight) hx
  have hsource :
      (FK.openSub (rlc_connectorCentralFaceFiniteGraph
          rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft)
          rlc_retainedChoiceAuditConfig ⊔
        rlc_connectorTraceWiring
          rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft).Reachable
        (rlc_connectorRightAnchor rlc_retainedChoiceAuditRight) y :=
    hright.mono le_sup_right |>.trans (hxy.mono le_sup_left)
  rw [← rlc_openSub_centralFaceClosure_ambient,
    rlc_openSub_centralFaceClosure_eq_openSubgraphInduce] at hsource
  have hyReach : (y : Site 2) ∈ rlc_connectorCentralFaceReachSet
      rlc_retainedChoiceAuditRight rlc_retainedChoiceAuditLeft
      rlc_retainedChoiceAuditConfig := ⟨y.2, hsource⟩
  exact rlc_rca_sourceSet_disjoint_left
    (rlc_rca_reachSet_subset_sourceSet hyReach) hy

end
end StatMech.Universality
