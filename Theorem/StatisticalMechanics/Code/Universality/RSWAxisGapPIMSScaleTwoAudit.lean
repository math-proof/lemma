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
import Def.StatisticalMechanics.Code.Universality.RSWAxisGapPIMSScaleTwoAudit
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_scaleTwoAxisGapRestrictedConfig_failure :
    rlc_scaleTwoAxisGapRestrictedConfig ∉
      rlc_finiteAxisGapConnectorEvent rlc_scaleTwoDoubleFailureGap := by
  intro hfinite
  have hgap : rlc_scaleTwoDoubleFailureConfig ∈
      rlc_axisGapConnectorEvent rlc_scaleTwoDoubleFailureGap :=
    (rlc_axisGapConnectorEvent_iff_finite
      rlc_scaleTwoDoubleFailureGap rlc_scaleTwoDoubleFailureConfig).mpr
      hfinite
  exact rlc_scaleTwoDoubleFailure_original_failure
    (rlc_mixedAxisGapConnectorEvent_subset_mixedWiredConnectorEvent
      rlc_scaleTwoDoubleFailureGap
      (rq1_axisGapConnectorEvent_subset_mixedAxisGapConnectorEvent
        rlc_scaleTwoDoubleFailureGap
        rlc_scaleTwoDoubleFailure_exposedPaths_disjoint hgap))

theorem rlc_scaleTwoAxisGap_seed_no_allowed_neighbor
    {v : Site 2}
    (hv : v ∈ rlc_connectorAllowed rlc_scaleTwoDoubleFailureRight
      rlc_scaleTwoDoubleFailureLeft)
    (hadj : (hypercubicLattice 2).Adj (![0, -1] : Site 2) v) : False := by
  have hvCand := mem_candFinset_of_adj 2 (![0, -1] : Site 2) v hadj
  rw [candFinset_face] at hvCand
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvCand
  have hvBarrier := (Finset.mem_sdiff.mp hv).2
  rcases hvCand with rfl | rfl | rfl | rfl <;> apply hvBarrier <;>
    rw [rlc_connectorBarrier,
      rlc_scaleTwoDoubleFailure_right_vertices,
      rlc_scaleTwoDoubleFailure_left_vertices] <;>
    simp [rlc_flipX, rlc_flipXFun]

theorem rlc_scaleTwoAxisGapRegion_eq_singleton :
    rlc_axisGapRegion rlc_scaleTwoDoubleFailureGap =
      {(![0, -1] : Site 2)} := by
  ext z
  constructor
  · intro hz
    have hzSet : z ∈ rlc_axisGapRegionSet
        rlc_scaleTwoDoubleFailureGap := by
      simpa [rlc_axisGapRegion] using hz
    obtain ⟨hzAllowed, _hseedAllowed, hreach⟩ := hzSet
    obtain ⟨w⟩ := hreach
    cases w with
    | nil =>
        simp [rlc_scaleTwoDoubleFailureGap,
          RlcAxisBarrierGap.seedVertex]
    | @cons _ b _ hab _ =>
        rw [SimpleGraph.induce_adj] at hab
        exact False.elim
          (rlc_scaleTwoAxisGap_seed_no_allowed_neighbor b.2 (by
            simpa [rlc_scaleTwoDoubleFailureGap,
              RlcAxisBarrierGap.seedVertex] using hab))
  · intro hz
    simp only [Finset.mem_singleton] at hz
    subst z
    simpa [rlc_scaleTwoDoubleFailureGap,
      RlcAxisBarrierGap.seedVertex] using
      (rlc_scaleTwoDoubleFailureGap.seedVertex_mem_region_of_lt
        (by norm_num) (by norm_num [rlc_scaleTwoDoubleFailureGap]))

theorem rlc_scaleTwoAxisGap_westEdge_mem :
    s((![-1, -1] : Site 2), ![0, -1]) ∈
      rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap := by
  rw [rlc_axisGapEdges, Finset.mem_union]
  left
  rw [Finset.mem_filter]
  exact ⟨by
      rw [mem_edgesWithinFinset]
      exact ⟨![-1, -1], by simp [rlc_connectorBox, mem_rect],
        ![0, -1], by simp [rlc_connectorBox, mem_rect], rfl⟩,
    ⟨![0, -1], by
      rw [rlc_scaleTwoAxisGapRegion_eq_singleton]
      simp, Sym2.mem_mk_right _ _⟩⟩

theorem rlc_scaleTwoAxisGap_leftEdge_mem :
    s((![0, -1] : Site 2), ![0, 0]) ∈
      rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap := by
  rw [rlc_axisGapEdges, Finset.mem_union]
  left
  rw [Finset.mem_filter]
  exact ⟨by
      rw [mem_edgesWithinFinset]
      exact ⟨![0, -1], by simp [rlc_connectorBox, mem_rect],
        ![0, 0], by simp [rlc_connectorBox, mem_rect], rfl⟩,
    ⟨![0, -1], by
      rw [rlc_scaleTwoAxisGapRegion_eq_singleton]
      simp, Sym2.mem_mk_left _ _⟩⟩


end
end StatMech.Universality
