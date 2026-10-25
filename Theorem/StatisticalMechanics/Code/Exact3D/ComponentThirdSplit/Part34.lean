/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part36
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ} :
    k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint ↔
      finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ k ∧
        k ≤ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card := by
  constructor
  · intro hk
    have hkfilter :
        k ∈
          (Finset.range
            ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card + 1)).filter
            (fun k =>
              finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                hasGhost hasOrigin hasEndpoint ≤ k) := by
      change
        k ∈
          (Finset.range
            ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card + 1)).filter
            (fun k =>
              finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                hasGhost hasOrigin hasEndpoint ≤ k) at hk
      exact hk
    exact
      ⟨(Finset.mem_filter.mp hkfilter).2,
        Nat.lt_succ_iff.mp
          (Finset.mem_range.mp (Finset.mem_filter.mp hkfilter).1)⟩
  · rintro ⟨hthreshold, hcard⟩
    unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hcard), hthreshold⟩

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_threshold_le
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (hk :
      k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint) :
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
      hasGhost hasOrigin hasEndpoint ≤ k :=
  (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff.mp
    hk).1

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_card_le
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (hk :
      k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint) :
    k ≤ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card :=
  (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff.mp
    hk).2

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_nonempty_iff
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint).Nonempty ↔
      finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card := by
  constructor
  · rintro ⟨k, hk⟩
    have hk' :=
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff.mp
        hk
    exact le_trans hk'.1 hk'.2
  · intro h
    exact
      ⟨finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint,
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff.mpr
          ⟨le_rfl, h⟩⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_empty_iff
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint =
        ∅ ↔
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card <
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint := by
  constructor
  · intro hidx
    by_contra hnot
    have hle :
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint ≤
          (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card :=
      Nat.le_of_not_lt hnot
    have hnonempty :
        (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
            v hasGhost hasOrigin hasEndpoint).Nonempty :=
      (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_nonempty_iff
        v hasGhost hasOrigin hasEndpoint).mpr hle
    rw [hidx] at hnonempty
    simp at hnonempty
  · intro hlt
    ext k
    constructor
    · intro hk
      have hk' :=
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff.mp
          hk
      omega
    · intro hk
      simp at hk

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint =
      Finset.Icc
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint)
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card := by
  ext k
  simp [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ} :
    k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint ↔
      finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ k ∧
        k ≤ (2 * n + 1) ^ 3 - 2 := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff,
    finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
      hv,
    StatMech.FK.ecz_boxVerts_card]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_nonempty_iff_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint).Nonempty ↔
      finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤
        (2 * n + 1) ^ 3 - 2 := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_nonempty_iff,
    finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
      hv,
    StatMech.FK.ecz_boxVerts_card]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_empty_iff_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint =
        ∅ ↔
      (2 * n + 1) ^ 3 - 2 <
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_empty_iff,
    finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
      hv,
    StatMech.FK.ecz_boxVerts_card]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint =
      Finset.Icc
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint)
        ((2 * n + 1) ^ 3 - 2) := by
  ext k
  simp [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff_box_volume_sub_two_of_boundary
      hv]

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_false_false_false_eq_Icc_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false false =
      Finset.Icc 4 ((2 * n + 1) ^ 3 - 2) := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv false false false

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_false_false_true_eq_Icc_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false true =
      Finset.Icc 3 ((2 * n + 1) ^ 3 - 2) := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv false false true

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_false_true_false_eq_Icc_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true false =
      Finset.Icc 3 ((2 * n + 1) ^ 3 - 2) := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv false true false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_false_true_true_eq_Icc_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true true =
      Finset.Icc 2 ((2 * n + 1) ^ 3 - 2) := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv false true true

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_true_false_false_eq_Icc_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false false =
      Finset.Icc 3 ((2 * n + 1) ^ 3 - 2) := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv true false false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_true_false_true_eq_Icc_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false true =
      Finset.Icc 2 ((2 * n + 1) ^ 3 - 2) := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv true false true

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_true_true_false_eq_Icc_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true false =
      Finset.Icc 2 ((2 * n + 1) ^ 3 - 2) := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv true true false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_true_true_true_eq_Icc_box_volume_sub_two_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true true =
      Finset.Icc 1 ((2 * n + 1) ^ 3 - 2) := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv true true true

end Exact3D
end StatMech
