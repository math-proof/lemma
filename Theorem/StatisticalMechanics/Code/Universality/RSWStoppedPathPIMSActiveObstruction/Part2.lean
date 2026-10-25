/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedPathPIMSActiveObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSScaleTwoAudit.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Def.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSActiveObstruction
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_activeGap_left_neighbor
    {x y : RlcConnectorVertex 1}
    (hx : rlc_connectorOnLeft rlc_traceSplitCounterexampleLeft x)
    (hxy : (rlc_axisGapFiniteGraph
      rlc_windingSideCounterexampleGap).Adj x y) :
    ((x : Site 2) = ![-2, 0] ∧ (y : Site 2) = ![-1, 0]) ∨
      ((x : Site 2) = ![-1, 1] ∧ (y : Site 2) = ![-1, 0]) ∨
      ((x : Site 2) = ![0, 1] ∧ (y : Site 2) = ![0, 0]) := by
  have hxBarrier : (x : Site 2) ∈ rlc_connectorBarrier
      rlc_traceSplitCounterexampleRight rlc_traceSplitCounterexampleLeft := by
    change (x : Site 2) ∈
      rlc_pathVertices rlc_traceSplitCounterexampleLeft.1 at hx
    rw [rlc_connectorBarrier]
    simp only [Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr hx))
  have hxNotRegion : (x : Site 2) ∉
      rlc_axisGapRegion rlc_windingSideCounterexampleGap := by
    intro hxRegion
    exact rlc_axisGapRegion_not_barrier hxRegion hxBarrier
  have hyRegion : (y : Site 2) ∈
      rlc_axisGapRegion rlc_windingSideCounterexampleGap := by
    have hsupport : s((x : Site 2), (y : Site 2)) ∈
        rlc_axisGapEdges rlc_windingSideCounterexampleGap := hxy.2
    rw [rlc_axisGapEdges, Finset.mem_union] at hsupport
    rcases hsupport with hinterior | hfirst
    · obtain ⟨_hedge, z, hzRegion, hzEdge⟩ :=
        Finset.mem_filter.mp hinterior
      rw [Sym2.mem_iff] at hzEdge
      rcases hzEdge with hzEdge | hzEdge
      · exact False.elim (hxNotRegion (hzEdge ▸ hzRegion))
      · exact hzEdge ▸ hzRegion
    · have hedge : s((x : Site 2), (y : Site 2)) =
          s((![0, -1] : Site 2), ![0, 0]) := by
        simpa [rlc_windingSideCounterexampleGap,
          RlcAxisBarrierGap.firstEdge,
          RlcAxisBarrierGap.lowerVertex,
          RlcAxisBarrierGap.seedVertex] using hfirst
      rw [Sym2.eq_iff] at hedge
      rcases hedge with ⟨hxEq, _⟩ | ⟨hxEq, _⟩ <;>
        rw [rlc_connectorOnLeft,
          rlc_traceSplitCounterexample_left_vertices, hxEq] at hx <;>
        simp at hx
  have hyCases := rlc_activeGap_region_cases hyRegion
  have hxVertices := hx
  rw [rlc_connectorOnLeft,
    rlc_traceSplitCounterexample_left_vertices] at hxVertices
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxVertices
  have hadj := hxy.1
  rcases hxVertices with hxv | hxv | hxv | hxv <;>
    rcases hyCases with hyv | hyv | hyv <;>
    rw [hxv, hyv] at hadj ⊢ <;>
    simp [hypercubicLattice_adj, Fin.sum_univ_two] at hadj ⊢

theorem rlc_activeGap_failure_of_leftCut_closed
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex 1)))
    (hA : rho s(⟨![-2, 0], by simp [mem_rect]⟩,
      ⟨![-1, 0], by simp [mem_rect]⟩) = false)
    (hB : rho s(⟨![-1, 1], by simp [mem_rect]⟩,
      ⟨![-1, 0], by simp [mem_rect]⟩) = false)
    (hC : rho s(⟨![0, 1], by simp [mem_rect]⟩,
      ⟨![0, 0], by simp [mem_rect]⟩) = false) :
    rho ∉ rlc_finiteAxisGapConnectorEvent
      rlc_windingSideCounterexampleGap := by
  rintro ⟨x, y, hx, hy, hreach⟩
  obtain ⟨w⟩ := hreach
  cases w.reverse with
  | nil =>
      have hdisj : Disjoint
          (rlc_pathVertices rlc_traceSplitCounterexampleRight.1)
          (rlc_pathVertices rlc_traceSplitCounterexampleLeft.1) := by
        rw [Finset.disjoint_left,
          rlc_traceSplitCounterexample_right_vertices,
          rlc_traceSplitCounterexample_left_vertices]
        simp
      exact Finset.disjoint_left.mp hdisj hx hy
  | @cons _ z _ hyz _ =>
      rw [FK.openSub_adj] at hyz
      rcases rlc_activeGap_left_neighbor hy hyz.1 with
        ⟨hyA, hzA⟩ | ⟨⟨hyB, hzB⟩ | ⟨hyC, hzC⟩⟩
      · have hedge : s(y, z) =
            s(⟨![-2, 0], by simp [mem_rect]⟩,
              ⟨![-1, 0], by simp [mem_rect]⟩) := by
          apply Sym2.map.injective Subtype.val_injective
          simp only [Sym2.map_mk]
          rw [hyA, hzA]
        rw [hedge, hA] at hyz
        simp at hyz
      · have hedge : s(y, z) =
            s(⟨![-1, 1], by simp [mem_rect]⟩,
              ⟨![-1, 0], by simp [mem_rect]⟩) := by
          apply Sym2.map.injective Subtype.val_injective
          simp only [Sym2.map_mk]
          rw [hyB, hzB]
        rw [hedge, hB] at hyz
        simp at hyz
      · have hedge : s(y, z) =
            s(⟨![0, 1], by simp [mem_rect]⟩,
              ⟨![0, 0], by simp [mem_rect]⟩) := by
          apply Sym2.map.injective Subtype.val_injective
          simp only [Sym2.map_mk]
          rw [hyC, hzC]
        rw [hedge, hC] at hyz
        simp at hyz

theorem rlc_activeGapDoubleFailureConfig_failure :
    rlc_activeGapDoubleFailureConfig ∉
      rlc_finiteAxisGapConnectorEvent
        rlc_windingSideCounterexampleGap := by
  apply rlc_activeGap_failure_of_leftCut_closed
  all_goals
    simp [rlc_activeGapDoubleFailureConfig, Sym2.map_mk]

theorem rlc_activeGapDoubleFailureConfig_PIMS_cut_closed :
    let rho := rlc_axisGapPIMSReflectedConfig
      rlc_windingSideCounterexampleGap rlc_activeGapDoubleFailureConfig
    rho s(⟨![-2, 0], by simp [mem_rect]⟩,
        ⟨![-1, 0], by simp [mem_rect]⟩) = false ∧
      rho s(⟨![-1, 1], by simp [mem_rect]⟩,
        ⟨![-1, 0], by simp [mem_rect]⟩) = false ∧
      rho s(⟨![0, 1], by simp [mem_rect]⟩,
        ⟨![0, 0], by simp [mem_rect]⟩) = false := by
  dsimp only
  constructor
  · rw [rlc_axisGapPIMSReflectedConfig_apply]
    have herase :
        (s(⟨![-2, 0], by simp [mem_rect]⟩,
          ⟨![-1, 0], by simp [mem_rect]⟩) :
            Sym2 (RlcConnectorVertex 1)).map Subtype.val =
          s((![-2, 0] : Site 2), ![-1, 0]) := by rfl
    rw [herase]
    have hpims : rlc_pimsEdgeEquiv
        s((![-2, 0] : Site 2), ![-1, 0]) =
          s((![1, -1] : Site 2), ![1, 0]) := by
      simpa using rlc_pimsEdgeEquiv_horizontal (-2) 0
    rw [hpims,
      rlc_axisGapAmbientConfig_supportEdge
        rlc_windingSideCounterexampleGap
        rlc_activeGapDoubleFailureConfig rlc_activeGap_sourceA_mem]
    simp [rlc_activeGapDoubleFailureConfig, rlc_axisGapEdgeLift_map]
  · constructor
    · rw [rlc_axisGapPIMSReflectedConfig_apply]
      have herase :
          (s(⟨![-1, 1], by simp [mem_rect]⟩,
            ⟨![-1, 0], by simp [mem_rect]⟩) :
              Sym2 (RlcConnectorVertex 1)).map Subtype.val =
            s((![-1, 0] : Site 2), ![-1, 1]) := by
        simp [Sym2.map_mk, Sym2.eq_swap]
      rw [herase]
      have hpims : rlc_pimsEdgeEquiv
          s((![-1, 0] : Site 2), ![-1, 1]) =
            s((![0, 0] : Site 2), ![1, 0]) := by
        simpa using rlc_pimsEdgeEquiv_vertical (-1) 0
      rw [hpims,
        rlc_axisGapAmbientConfig_supportEdge
          rlc_windingSideCounterexampleGap
          rlc_activeGapDoubleFailureConfig rlc_activeGap_sourceB_mem]
      simp [rlc_activeGapDoubleFailureConfig, rlc_axisGapEdgeLift_map]
    · rw [rlc_axisGapPIMSReflectedConfig_apply]
      have herase :
          (s(⟨![0, 1], by simp [mem_rect]⟩,
            ⟨![0, 0], by simp [mem_rect]⟩) :
              Sym2 (RlcConnectorVertex 1)).map Subtype.val =
            s((![0, 0] : Site 2), ![0, 1]) := by
        simp [Sym2.map_mk, Sym2.eq_swap]
      rw [herase]
      have hpims : rlc_pimsEdgeEquiv
          s((![0, 0] : Site 2), ![0, 1]) =
            s((![-1, 0] : Site 2), ![0, 0]) := by
        simpa using rlc_pimsEdgeEquiv_vertical 0 0
      rw [hpims,
        rlc_axisGapAmbientConfig_supportEdge
          rlc_windingSideCounterexampleGap
          rlc_activeGapDoubleFailureConfig rlc_activeGap_sourceC_mem]
      simp [rlc_activeGapDoubleFailureConfig, rlc_axisGapEdgeLift_map]

theorem rlc_activeGapDoubleFailureConfig_PIMS_failure :
    rlc_axisGapPIMSReflectedConfig rlc_windingSideCounterexampleGap
        rlc_activeGapDoubleFailureConfig ∉
      rlc_finiteAxisGapConnectorEvent
        rlc_windingSideCounterexampleGap := by
  obtain ⟨hA, hB, hC⟩ :=
    rlc_activeGapDoubleFailureConfig_PIMS_cut_closed
  exact rlc_activeGap_failure_of_leftCut_closed _ hA hB hC


theorem rlc_activeExtremalGap_doubleFailure :
    (rlc_extremalPairCandidate
        (rlc_traceSplitCounterexampleRight,
          rlc_traceSplitCounterexampleLeft)).Nonempty ∧
      rlc_activeGapDoubleFailureConfig ∉
        rlc_finiteAxisGapConnectorEvent
          rlc_windingSideCounterexampleGap ∧
      rlc_axisGapPIMSReflectedConfig rlc_windingSideCounterexampleGap
          rlc_activeGapDoubleFailureConfig ∉
        rlc_finiteAxisGapConnectorEvent
          rlc_windingSideCounterexampleGap :=
  ⟨⟨rlc_extremalSelectionCounterexampleConfig,
      rlc_extremalSelection_extremalPairCandidate⟩,
    rlc_activeGapDoubleFailureConfig_failure,
    rlc_activeGapDoubleFailureConfig_PIMS_failure⟩

theorem rlc_activeExtremalGap_not_stoppedProvenance :
    ¬ Nonempty (RlcStoppedExtremalAxisGapProvenance
      rlc_windingSideCounterexampleGap (by norm_num)
        (by norm_num [rlc_windingSideCounterexampleGap])) := by
  rintro ⟨S⟩
  exact rlc_activeGapDoubleFailureConfig_PIMS_failure
    (S.pims_success_of_failure rlc_activeGapDoubleFailureConfig
      rlc_activeGapDoubleFailureConfig_failure)


theorem not_rlc_extremalStrataCarryStoppedPIMSProvenance :
    ¬ RlcExtremalStrataCarryStoppedPIMSProvenance 1 := by
  intro hcarry
  exact rlc_activeExtremalGap_not_stoppedProvenance
    (hcarry rlc_traceSplitCounterexampleRight
      rlc_traceSplitCounterexampleLeft
      rlc_windingSideCounterexampleGap (by norm_num)
      (by norm_num [rlc_windingSideCounterexampleGap])
      ⟨rlc_extremalSelectionCounterexampleConfig,
        rlc_extremalSelection_extremalPairCandidate⟩)

end
end StatMech.Universality
