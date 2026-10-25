/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWAxisGapPIMSScaleTwoAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWStoppedPathPIMSProvenance.Part3
import Theorem.StatisticalMechanics.Code.Universality.QOneRSWActiveSeed.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorActualSelectedObstruction
import Def.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSScaleTwoAudit.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_scaleTwoAxisGap_left_neighbor
    {x y : RlcConnectorVertex 2}
    (hx : rlc_connectorOnLeft rlc_scaleTwoDoubleFailureLeft x)
    (hxy : (rlc_axisGapFiniteGraph
      rlc_scaleTwoDoubleFailureGap).Adj x y) :
    (x : Site 2) = ![0, 0] ∧ (y : Site 2) = ![0, -1] := by
  have hxNotSeed : (x : Site 2) ≠ ![0, -1] := by
    intro hxSeed
    rw [rlc_connectorOnLeft,
      rlc_scaleTwoDoubleFailure_left_vertices] at hx
    simp [hxSeed] at hx
  have hySeed : (y : Site 2) = ![0, -1] := by
    have hsupport : s((x : Site 2), (y : Site 2)) ∈
        rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap := hxy.2
    rw [rlc_axisGapEdges, Finset.mem_union] at hsupport
    rcases hsupport with hinterior | hfirst
    · obtain ⟨_hedge, z, hzRegion, hzEdge⟩ :=
        Finset.mem_filter.mp hinterior
      rw [rlc_scaleTwoAxisGapRegion_eq_singleton] at hzRegion
      simp only [Finset.mem_singleton] at hzRegion
      subst z
      rw [Sym2.mem_iff] at hzEdge
      rcases hzEdge with hzEdge | hzEdge
      · exact False.elim (hxNotSeed hzEdge.symm)
      · exact hzEdge.symm
    · have hedge : s((x : Site 2), (y : Site 2)) =
          s((![0, -2] : Site 2), ![0, -1]) := by
        simpa [rlc_scaleTwoDoubleFailureGap,
          RlcAxisBarrierGap.firstEdge,
          RlcAxisBarrierGap.lowerVertex,
          RlcAxisBarrierGap.seedVertex] using hfirst
      rw [Sym2.eq_iff] at hedge
      rcases hedge with ⟨hxE, _⟩ | ⟨hxC, _⟩
      · rw [rlc_connectorOnLeft,
          rlc_scaleTwoDoubleFailure_left_vertices] at hx
        simp [hxE] at hx
      · exact False.elim (hxNotSeed hxC)
  refine ⟨?_, hySeed⟩
  have hxVertices := hx
  rw [rlc_connectorOnLeft,
    rlc_scaleTwoDoubleFailure_left_vertices] at hxVertices
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxVertices
  have hadj := hxy.1
  rw [hySeed] at hadj
  rcases hxVertices with hxv | hxv | hxv | hxv | hxv | hxv | hxv <;>
    rw [hxv] at hadj ⊢ <;>
    simp [hypercubicLattice_adj, Fin.sum_univ_two] at hadj ⊢


theorem rlc_scaleTwoAxisGap_right_neighbor
    {x y : RlcConnectorVertex 2}
    (hx : rlc_connectorOnRight rlc_scaleTwoDoubleFailureRight x)
    (hxy : (rlc_axisGapFiniteGraph
      rlc_scaleTwoDoubleFailureGap).Adj x y) :
    ((x : Site 2) = ![0, -2] ∨ (x : Site 2) = ![1, -1]) ∧
      (y : Site 2) = ![0, -1] := by
  have hxNotSeed : (x : Site 2) ≠ ![0, -1] := by
    intro hxSeed
    rw [rlc_connectorOnRight,
      rlc_scaleTwoDoubleFailure_right_vertices] at hx
    simp [hxSeed] at hx
  have hySeed : (y : Site 2) = ![0, -1] := by
    have hsupport : s((x : Site 2), (y : Site 2)) ∈
        rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap := hxy.2
    rw [rlc_axisGapEdges, Finset.mem_union] at hsupport
    rcases hsupport with hinterior | hfirst
    · obtain ⟨_hedge, z, hzRegion, hzEdge⟩ :=
        Finset.mem_filter.mp hinterior
      rw [rlc_scaleTwoAxisGapRegion_eq_singleton] at hzRegion
      simp only [Finset.mem_singleton] at hzRegion
      subst z
      rw [Sym2.mem_iff] at hzEdge
      rcases hzEdge with hzEdge | hzEdge
      · exact False.elim (hxNotSeed hzEdge.symm)
      · exact hzEdge.symm
    · have hedge : s((x : Site 2), (y : Site 2)) =
          s((![0, -2] : Site 2), ![0, -1]) := by
        simpa [rlc_scaleTwoDoubleFailureGap,
          RlcAxisBarrierGap.firstEdge,
          RlcAxisBarrierGap.lowerVertex,
          RlcAxisBarrierGap.seedVertex] using hfirst
      rw [Sym2.eq_iff] at hedge
      rcases hedge with ⟨_, hyC⟩ | ⟨hxC, _⟩
      · exact hyC
      · exact False.elim (hxNotSeed hxC)
  refine ⟨?_, hySeed⟩
  have hxVertices := hx
  rw [rlc_connectorOnRight,
    rlc_scaleTwoDoubleFailure_right_vertices] at hxVertices
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxVertices
  have hadj := hxy.1
  rw [hySeed] at hadj
  rcases hxVertices with hxv | hxv | hxv | hxv | hxv | hxv | hxv <;>
    rw [hxv] at hadj ⊢ <;>
    simp [hypercubicLattice_adj, Fin.sum_univ_two] at hadj ⊢

theorem rlc_scaleTwoAxisGap_failure_of_leftEdge_closed
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex 2)))
    (hclosed : rho
      s(⟨![0, -1], by simp [mem_rect]⟩,
        ⟨![0, 0], by simp [mem_rect]⟩) = false) :
    rho ∉ rlc_finiteAxisGapConnectorEvent
      rlc_scaleTwoDoubleFailureGap := by
  rintro ⟨x, y, hx, hy, hreach⟩
  obtain ⟨w⟩ := hreach
  cases w.reverse with
  | nil =>
      exact Finset.disjoint_left.mp
        rlc_scaleTwoDoubleFailure_exposedPaths_disjoint hx hy
  | @cons _ z _ hyz _ =>
      rw [FK.openSub_adj] at hyz
      obtain ⟨hyI, hzC⟩ :=
        rlc_scaleTwoAxisGap_left_neighbor hy hyz.1
      have hedge : s(y, z) =
          s(⟨![0, -1], by simp [mem_rect]⟩,
            ⟨![0, 0], by simp [mem_rect]⟩) := by
        apply Sym2.map.injective Subtype.val_injective
        simp only [Sym2.map_mk]
        rw [hyI, hzC, Sym2.eq_swap]
      rw [hedge, hclosed] at hyz
      simp at hyz

theorem rlc_scaleTwoAxisGapDoubleFailureConfig_failure :
    rlc_scaleTwoAxisGapDoubleFailureConfig ∉
      rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap := by
  apply rlc_scaleTwoAxisGap_failure_of_leftEdge_closed
  simp [rlc_scaleTwoAxisGapDoubleFailureConfig, Sym2.map_mk]

theorem rlc_scaleTwoAxisGapDoubleFailureConfig_PIMS_leftEdge_closed :
    rlc_axisGapPIMSReflectedConfig rlc_scaleTwoDoubleFailureGap
      rlc_scaleTwoAxisGapDoubleFailureConfig
      s(⟨![0, -1], by simp [mem_rect]⟩,
        ⟨![0, 0], by simp [mem_rect]⟩) = false := by
  rw [rlc_axisGapPIMSReflectedConfig_apply]
  have herase :
      (s(⟨![0, -1], by simp [mem_rect]⟩,
        ⟨![0, 0], by simp [mem_rect]⟩) :
          Sym2 (RlcConnectorVertex 2)).map Subtype.val =
        s((![0, -1] : Site 2), ![0, 0]) := by
    rfl
  rw [herase]
  have hpims : rlc_pimsEdgeEquiv
      s((![0, -1] : Site 2), ![0, 0]) =
      s((![-1, -1] : Site 2), ![0, -1]) := by
    simpa using rlc_pimsEdgeEquiv_vertical 0 (-1)
  rw [hpims, rlc_axisGapAmbientConfig_supportEdge
    rlc_scaleTwoDoubleFailureGap rlc_scaleTwoAxisGapDoubleFailureConfig
      rlc_scaleTwoAxisGap_westEdge_mem]
  simp [rlc_scaleTwoAxisGapDoubleFailureConfig,
    rlc_axisGapEdgeLift_map]

theorem rlc_scaleTwoAxisGapDoubleFailureConfig_PIMS_failure :
    rlc_axisGapPIMSReflectedConfig rlc_scaleTwoDoubleFailureGap
        rlc_scaleTwoAxisGapDoubleFailureConfig ∉
      rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap :=
  rlc_scaleTwoAxisGap_failure_of_leftEdge_closed _
    rlc_scaleTwoAxisGapDoubleFailureConfig_PIMS_leftEdge_closed


theorem rlc_scaleTwoAxisGap_doubleFailure :
    rlc_scaleTwoAxisGapDoubleFailureConfig ∉
        rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap ∧
      rlc_axisGapPIMSReflectedConfig rlc_scaleTwoDoubleFailureGap
          rlc_scaleTwoAxisGapDoubleFailureConfig ∉
        rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap :=
  ⟨rlc_scaleTwoAxisGapDoubleFailureConfig_failure,
    rlc_scaleTwoAxisGapDoubleFailureConfig_PIMS_failure⟩


theorem rlc_scaleTwoAxisGap_not_failureSelectedSideTopology :
    ¬ RlcAxisGapPIMSFailureSelectedSideTopology
      rlc_scaleTwoDoubleFailureGap (by norm_num)
        (by norm_num [rlc_scaleTwoDoubleFailureGap]) := by
  intro htopology
  exact rlc_scaleTwoAxisGapDoubleFailureConfig_PIMS_failure
    (rlc_axisGapPIMS_success_of_failureSelectedSideTopology
      rlc_scaleTwoDoubleFailureGap (by norm_num)
      (by norm_num [rlc_scaleTwoDoubleFailureGap]) htopology
      rlc_scaleTwoAxisGapDoubleFailureConfig
      rlc_scaleTwoAxisGapDoubleFailureConfig_failure)

end
end StatMech.Universality
