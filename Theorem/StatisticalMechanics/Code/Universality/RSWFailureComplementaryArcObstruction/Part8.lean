/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
import Def.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part8
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

theorem rlc_stdf_right_boundary_edge_classify {u v : Site 2}
    (hu : u ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1)
    (hv : v ∉ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1)
    (hvBox : v ∈ rect (-4) 4 (-2) 2)
    (huv : (hypercubicLattice 2).Adj u v) :
    s(u, v) ∈ rlc_stdf_supportBoundaryEdges ∨
      s(u, v) ∈ rlc_stdf_nonSupportBoundaryEdges := by
  have hvCand := mem_candFinset_of_adj 2 u v huv
  rw [rlc_scaleTwoDoubleFailure_right_vertices] at hu hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [candFinset_face] at hvCand
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand
    rcases hvCand with rfl | rfl | rfl | rfl <;>
      simp [rlc_stdf_supportBoundaryEdges,
        rlc_stdf_nonSupportBoundaryEdges, mem_rect] at hv hvBox ⊢

theorem rlc_stdf_supportBoundaryEdge_pims_open
    {e : Sym2 (Site 2)} (he : e ∈ rlc_stdf_supportBoundaryEdges) :
    rlc_scaleTwoDoubleFailureConfig (rlc_pimsEdgeEquiv e) = true := by
  simp only [rlc_stdf_supportBoundaryEdges, Finset.mem_insert,
    Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · rw [show s((![-1, -2] : Site 2), ![0, -2]) =
        s(![-1, -2], ![-1 + 1, -2]) by norm_num,
      rlc_pimsEdgeEquiv_horizontal]
    simp [rlc_scaleTwoDoubleFailureConfig,
      rlc_scaleTwoDoubleFailureOpenEdges]
  · rw [show s((![0, -2] : Site 2), ![0, -1]) =
        s(![0, -2], ![0, -2 + 1]) by norm_num,
      rlc_pimsEdgeEquiv_vertical]
    simp [rlc_scaleTwoDoubleFailureConfig,
      rlc_scaleTwoDoubleFailureOpenEdges]
  · rw [show s((![0, -1] : Site 2), ![1, -1]) =
        s(![0, -1], ![0 + 1, -1]) by norm_num,
      rlc_pimsEdgeEquiv_horizontal]
    simp [rlc_scaleTwoDoubleFailureConfig,
      rlc_scaleTwoDoubleFailureOpenEdges]
  · rw [show s((![2, -2] : Site 2), ![2, -1]) =
        s(![2, -2], ![2, -2 + 1]) by norm_num,
      rlc_pimsEdgeEquiv_vertical]
    simp [rlc_scaleTwoDoubleFailureConfig,
      rlc_scaleTwoDoubleFailureOpenEdges]
  · rw [show s((![2, -1] : Site 2), ![2, 0]) =
        s(![2, -1], ![2, -1 + 1]) by norm_num,
      rlc_pimsEdgeEquiv_vertical]
    simp [rlc_scaleTwoDoubleFailureConfig,
      rlc_scaleTwoDoubleFailureOpenEdges]

theorem rlc_stdf_right_left_disjoint {z : Site 2}
    (hzRight : z ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1)
    (hzLeft : z ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureLeft.1) :
    False := by
  rw [rlc_scaleTwoDoubleFailure_right_vertices] at hzRight
  rw [rlc_scaleTwoDoubleFailure_left_vertices] at hzLeft
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzRight hzLeft
  rcases hzRight with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all

theorem rlc_stdf_reflected_open_step {u v : Site 2}
    (hu : u ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1)
    (hvBox : v ∈ rect (-4) 4 (-2) 2)
    (huv : (hypercubicLattice 2).Adj u v)
    (hopen : rlc_wiredConnectorConfig
      rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft
      (rlc_mixedAxisGapEdges rlc_scaleTwoDoubleFailureGap)
      (rlc_dualReflectConfig rlc_scaleTwoDoubleFailureConfig)
      s(u, v) = true) :
    v ∈ rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1 := by
  let e : Sym2 (Site 2) := s(u, v)
  by_cases hp : e ∈
      rlc_pathEdges rlc_scaleTwoDoubleFailureRight.1 ∪
        rlc_pathEdges rlc_scaleTwoDoubleFailureLeft.1
  · rw [Finset.mem_union] at hp
    rcases hp with hright | hleft
    · exact (rlc_pathEdge_endpoints_mem_vertices
        rlc_scaleTwoDoubleFailureRight.1 hright).2
    · exact False.elim (rlc_stdf_right_left_disjoint hu
        (rlc_pathEdge_endpoints_mem_vertices
          rlc_scaleTwoDoubleFailureLeft.1 hleft).1)
  · rw [rlc_wiredConnectorConfig, if_neg hp, rlc_maskConfig] at hopen
    split at hopen
    next hU =>
      by_contra hv
      have hclass := rlc_stdf_right_boundary_edge_classify hu hv hvBox huv
      have hsupport : e ∈ rlc_stdf_supportBoundaryEdges := by
        rcases hclass with hsupport | hnonSupport
        · exact hsupport
        · exact False.elim
            (rlc_stdf_nonSupportBoundaryEdges_not_mixed hnonSupport hU)
      have hpimsOpen := rlc_stdf_supportBoundaryEdge_pims_open hsupport
      have hdual : rlc_dualReflectConfig rlc_scaleTwoDoubleFailureConfig e =
          false := by
        rw [rlc_dualReflectConfig_eq_pims, hpimsOpen]
        rfl
      rw [hdual] at hopen
      contradiction
    next _ => simp at hopen


theorem rlc_scaleTwoDoubleFailure_reflected_failure :
    rlc_dualReflectConfig rlc_scaleTwoDoubleFailureConfig ∉
      rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap := by
  intro hconn
  let B := rect (-4) 4 (-2) 2
  let eta := rlc_wiredConnectorConfig
    rlc_scaleTwoDoubleFailureRight rlc_scaleTwoDoubleFailureLeft
    (rlc_mixedAxisGapEdges rlc_scaleTwoDoubleFailureGap)
    (rlc_dualReflectConfig rlc_scaleTwoDoubleFailureConfig)
  have walk_stays {x y : B}
      (p : (openSubgraphInduce 2 eta B).Walk x y)
      (hx : (x : Site 2) ∈
        rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1) :
      (y : Site 2) ∈
        rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1 := by
    induction p with
    | nil => exact hx
    | @cons a b c hab p ih =>
        rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
        exact ih (rlc_stdf_reflected_open_step hx b.2 hab.1 hab.2)
  obtain ⟨p⟩ := hconn
  have hlower :
      (rlc_scaleTwoDoubleFailureGap.lowerVertex : Site 2) ∈
        rlc_pathVertices rlc_scaleTwoDoubleFailureRight.1 :=
    rlc_scaleTwoDoubleFailureGap.lowerVertex_mem_right
  have hupper := walk_stays p hlower
  rw [rlc_scaleTwoDoubleFailure_right_vertices] at hupper
  simp [rlc_scaleTwoDoubleFailureGap, RlcAxisBarrierGap.upperVertex] at hupper


theorem rlc_scaleTwoDoubleFailure_defectCut :
    RlcRelaxedLocalDefectsSeparateTraces rlc_scaleTwoDoubleFailureGap
      rlc_scaleTwoDoubleFailureConfig :=
  rlc_relaxedLocalDefectsSeparateTraces_of_dualReflect_failure
    rlc_scaleTwoDoubleFailureGap (by norm_num)
      (by norm_num [rlc_scaleTwoDoubleFailureGap])
      rlc_scaleTwoDoubleFailureConfig
      rlc_scaleTwoDoubleFailure_reflected_failure


theorem rlc_scaleTwoDoubleFailure_no_relaxedLocalTraceArc :
    ¬ RlcRelaxedLocalTraceArcExists rlc_scaleTwoDoubleFailureGap
      rlc_scaleTwoDoubleFailureConfig := by
  intro harc
  exact (rlc_relaxedLocalTraceArcExists_iff_not_defectCut
    rlc_scaleTwoDoubleFailureGap rlc_scaleTwoDoubleFailureConfig).mp harc
      rlc_scaleTwoDoubleFailure_defectCut


theorem rlc_scaleTwoDoubleFailure_not_failureComplementaryArcEscapes :
    ¬ RlcFailureComplementaryArcEscapesDefectCut
      rlc_scaleTwoDoubleFailureGap rlc_scaleTwoDoubleFailureConfig :=
  not_failureComplementaryArcEscapes_of_dualReflect_failure
    rlc_scaleTwoDoubleFailureGap (by norm_num)
      (by norm_num [rlc_scaleTwoDoubleFailureGap])
      rlc_scaleTwoDoubleFailureConfig
      rlc_scaleTwoDoubleFailure_reflected_failure


theorem rlc_scaleTwoDoubleFailure_not_failureSelectedExtremalTraceTopology :
    ¬ RlcFailureSelectedExtremalTraceTopology
      rlc_scaleTwoDoubleFailureGap := by
  intro htopology
  exact rlc_scaleTwoDoubleFailure_reflected_failure
    (rlc_dualReflect_success_of_failureSelectedExtremalTraceTopology
      rlc_scaleTwoDoubleFailureGap (by norm_num)
      (by norm_num [rlc_scaleTwoDoubleFailureGap]) htopology
      rlc_scaleTwoDoubleFailureConfig
      rlc_scaleTwoDoubleFailure_original_failure)


theorem rlc_failure_not_imply_failureComplementaryArcEscapesDefectCut :
    ¬ (∀ omega : ConfigSpace (Sym2 (Site 2)),
      omega ∉ rlc_mixedWiredConnectorEvent rlc_scaleTwoDoubleFailureGap →
        RlcFailureComplementaryArcEscapesDefectCut
          rlc_scaleTwoDoubleFailureGap omega) := by
  intro h
  exact rlc_scaleTwoDoubleFailure_not_failureComplementaryArcEscapes
    (h rlc_scaleTwoDoubleFailureConfig
      rlc_scaleTwoDoubleFailure_original_failure)

end Universality
end StatMech
