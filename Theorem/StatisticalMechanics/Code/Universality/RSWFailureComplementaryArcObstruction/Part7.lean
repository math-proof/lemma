/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWFailureComplementaryArcObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part4
import Def.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part7
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

theorem rlc_stdf_nonSupportBoundaryEdges_not_gap
    {e : Sym2 (Site 2)} (he : e ∈ rlc_stdf_nonSupportBoundaryEdges) :
    e ∉ rlc_axisGapEdges rlc_scaleTwoDoubleFailureGap := by
  intro hgap
  rcases rlc_stdf_axisGapEdge_location hgap with hfirst |
      ⟨z, hzCore, hzEdge⟩
  · simp only [rlc_stdf_nonSupportBoundaryEdges, Finset.mem_insert,
      Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [rlc_scaleTwoDoubleFailureGap, RlcAxisBarrierGap.firstEdge,
        RlcAxisBarrierGap.lowerVertex, RlcAxisBarrierGap.seedVertex] at hfirst
  · simp only [rlc_stdf_nonSupportBoundaryEdges, Finset.mem_insert,
      Finset.mem_singleton] at he
    simp only [rlc_stdf_gapRegionCore, Finset.mem_insert,
      Finset.mem_singleton] at hzCore
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hzCore with rfl | rfl | rfl <;> simp at hzEdge

theorem rlc_stdf_nonSupportBoundaryEdges_not_mixed
    {e : Sym2 (Site 2)} (he : e ∈ rlc_stdf_nonSupportBoundaryEdges) :
    e ∉ rlc_mixedAxisGapEdges rlc_scaleTwoDoubleFailureGap := by
  intro hmixed
  have hsupport := (Finset.mem_sdiff.mp hmixed).1
  simp only [Finset.mem_union] at hsupport
  rcases hsupport with (hgap | hright) | hleft
  · exact rlc_stdf_nonSupportBoundaryEdges_not_gap he hgap
  · simp only [rlc_stdf_nonSupportBoundaryEdges, Finset.mem_insert,
      Finset.mem_singleton] at he
    unfold rlc_reflectedPathEdges at hright
    rw [rlc_scaleTwoDoubleFailure_right_edges] at hright
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [rlc_flipX, rlc_flipXFun] at hright
  · simp only [rlc_stdf_nonSupportBoundaryEdges, Finset.mem_insert,
      Finset.mem_singleton] at he
    unfold rlc_reflectedPathEdges at hleft
    rw [rlc_scaleTwoDoubleFailure_left_edges] at hleft
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [rlc_flipX, rlc_flipXFun] at hleft

end Universality
end StatMech
