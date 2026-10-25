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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part47
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_zero_of_shellIndex_eq_empty
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool)
    (hidx :
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint =
        ∅) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint =
      0 := by
  unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
  rw [hidx]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_zero_of_unmarkedOptions_card_lt_threshold
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool)
    (hcard :
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card <
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint =
      0 :=
  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_zero_of_shellIndex_eq_empty
    β H n Ω v hasGhost hasOrigin hasEndpoint
    ((finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_empty_iff
      v hasGhost hasOrigin hasEndpoint).mpr hcard)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_zero_of_boundary_of_box_volume_sub_two_lt_threshold
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool)
    (hcard :
      (2 * n + 1) ^ 3 - 2 <
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint =
      0 :=
  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_zero_of_shellIndex_eq_empty
    β H n Ω v hasGhost hasOrigin hasEndpoint
    ((finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_empty_iff_box_volume_sub_two_of_boundary
      hv hasGhost hasOrigin hasEndpoint).mpr hcard)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint =
      ∑ k ∈
        Finset.Icc
          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint)
          ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint k := by
  unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_Icc_box_volume_sub_two_of_boundary
      hv hasGhost hasOrigin hasEndpoint]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_false_false_false_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v false false false =
      ∑ k ∈ Finset.Icc 4 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v false false false k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv false false false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_false_false_true_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v false false true =
      ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v false false true k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv false false true

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_false_true_false_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v false true false =
      ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v false true false k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv false true false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_false_true_true_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v false true true =
      ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v false true true k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv false true true

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_true_false_false_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v true false false =
      ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v true false false k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv true false false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_true_false_true_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v true false true =
      ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v true false true k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv true false true

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_true_true_false_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v true true false =
      ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v true true false k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv true true false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_true_true_true_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v true true true =
      ∑ k ∈ Finset.Icc 1 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v true true true k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv true true true

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_nonneg
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    0 ≤
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint := by
  classical
  unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
  exact Finset.sum_nonneg (fun k _hk =>
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_nonneg
      hβ hH n Ω v hasGhost hasOrigin hasEndpoint k)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_le_markedResidualThresholdShellImageSourceClassSum
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              hasGhost hasOrigin hasEndpoint),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) ≤
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint := by
  classical
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_unmarkedResidualCard_shell_sum
      β H n Ω v hv hasGhost hasOrigin hasEndpoint]
  unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
  exact Finset.sum_le_sum
    (fun k _hk =>
      by
        simpa [Finset.filter_filter, and_assoc] using
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_le_markedResidualExactCardImageSourceClassSum
            hβ hH n Ω v hasGhost hasOrigin hasEndpoint k)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_mem_iff
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    {S : Finset (Option (FK.boxVerts 3 n))} :
    S ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
          v hasGhost hasOrigin hasEndpoint k ↔
      ∃ R,
        R ∈ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset ∧
          R.card = k ∧
          finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R =
            S := by
  classical
  unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨R, hRfilter, hSR⟩
    exact
      ⟨R, (Finset.mem_filter.mp hRfilter).1,
        (Finset.mem_filter.mp hRfilter).2, hSR⟩
  · rintro ⟨R, hRpow, hRcard, hSR⟩
    exact Finset.mem_image.mpr
      ⟨R, Finset.mem_filter.mpr ⟨hRpow, hRcard⟩, hSR⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_unmarkedResidual_card_eq
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
          v hasGhost hasOrigin hasEndpoint k) :
    (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card = k := by
  classical
  rcases
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_mem_iff.mp
        hS with
    ⟨R, hRpow, hRcard, hSR⟩
  have hres :
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S = R := by
    ext x
    constructor
    · intro hx
      rcases
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_iff.mp
            hx with
        ⟨hxS, hxUnmarked⟩
      have hxUnion :
          x ∈ finiteBoundaryGhostSourceClassEndpointMarkedSources
                v hasGhost hasOrigin hasEndpoint ∪ R := by
        simpa [hSR] using hxS
      rcases Finset.mem_union.mp hxUnion with hxMarked | hxR
      · have hxnot :=
          (Finset.disjoint_left.mp
            (finiteBoundaryGhostSourceClassEndpointMarkedSources_disjoint_unmarkedOptions
              v hasGhost hasOrigin hasEndpoint)) hxMarked
        exact False.elim (hxnot hxUnmarked)
      · exact hxR
    · intro hxR
      exact
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_iff.mpr
          ⟨by
            have hxUnion :
                x ∈ finiteBoundaryGhostSourceClassEndpointMarkedSources
                      v hasGhost hasOrigin hasEndpoint ∪ R :=
              Finset.mem_union.mpr (Or.inr hxR)
            simpa [hSR] using hxUnion,
          (Finset.mem_powerset.mp hRpow) hxR⟩
  rw [hres, hRcard]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_card_eq
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
          v hasGhost hasOrigin hasEndpoint k) :
    S.card =
      (finiteBoundaryGhostSourceClassEndpointMarkedSources
        v hasGhost hasOrigin hasEndpoint).card + k := by
  classical
  rcases
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_mem_iff.mp
        hS with
    ⟨R, hRpow, hRcard, hSR⟩
  rw [← hSR]
  rw [
    finiteBoundaryGhostSourceClassEndpointMarkedSources_union_card_eq
      v hasGhost hasOrigin hasEndpoint hRpow,
    hRcard]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_zero_of_boundary_of_threshold_add_k_odd
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hodd :
      Odd
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint +
          k)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k =
      0 := by
  classical
  unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
  refine Finset.sum_eq_zero ?_
  intro S hS
  exact
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_eq_zero_of_not_mem_sourceClassSupport
      β H
      (by
        intro hSsupport
        have hEven :
            Even S.card :=
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_card_even
            hSsupport
        have hcard :
            S.card =
              (finiteBoundaryGhostSourceClassEndpointMarkedSources
                v hasGhost hasOrigin hasEndpoint).card + k :=
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_card_eq
            hS
        have hthreshold :
            finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                hasGhost hasOrigin hasEndpoint +
              (finiteBoundaryGhostSourceClassEndpointMarkedSources
                v hasGhost hasOrigin hasEndpoint).card =
              4 :=
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_add_markedSources_card_eq_four_of_boundary
            hv hasGhost hasOrigin hasEndpoint
        rw [hcard] at hEven
        rcases hEven with ⟨a, ha⟩
        rcases hodd with ⟨b, hb⟩
        omega)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_even_filter_sum_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint =
      ∑ k ∈
        (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint).filter
          (fun k =>
            Even
              (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
                  hasGhost hasOrigin hasEndpoint +
                k)),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint k := by
  classical
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases heven :
      Even
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint +
          k)
  · simp [heven]
  · have hodd :
        Odd
          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
              hasGhost hasOrigin hasEndpoint +
            k) :=
      Nat.not_even_iff_odd.mp heven
    simp [
      heven,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_zero_of_boundary_of_threshold_add_k_odd
        β H n Ω hv hasGhost hasOrigin hasEndpoint hodd]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_true_true_true_eq_even_filter_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v true true true =
      ∑ k ∈
        (Finset.Icc 1 ((2 * n + 1) ^ 3 - 2)).filter
          (fun k => Even (1 + k)),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v true true true k := by
  simpa [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_true_true_true_eq_Icc_box_volume_sub_two_of_boundary
      hv,
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_even_filter_sum_of_boundary
      β H n Ω hv true true true

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_ghost_mem_iff
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
          v hasGhost hasOrigin hasEndpoint k) :
    none ∈ S ↔ hasGhost = true := by
  classical
  rcases
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_mem_iff.mp
        hS with
    ⟨R, hRpow, _hRcard, hSR⟩
  constructor
  · intro hnoneS
    have hnoneUnion :
        none ∈ finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R := by
      simpa [hSR] using hnoneS
    rcases Finset.mem_union.mp hnoneUnion with hmarked | hR
    · simpa using
        (finiteBoundaryGhostSourceClassEndpointMarkedSources_mem_iff.mp
          hmarked)
    · have hUnmarked : none ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v :=
        (Finset.mem_powerset.mp hRpow) hR
      exact False.elim
        ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_mem_iff.mp
          hUnmarked).1 rfl)
  · intro hghost
    have hmarked :
        none ∈ finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint :=
      finiteBoundaryGhostSourceClassEndpointMarkedSources_mem_iff.mpr
        (Or.inl ⟨rfl, hghost⟩)
    have hnoneUnion :
        none ∈ finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R :=
      Finset.mem_union.mpr (Or.inl hmarked)
    simpa [hSR] using hnoneUnion

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_origin_mem_iff_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
          v hasGhost hasOrigin hasEndpoint k) :
    some (IsingFK.boxOrigin 3 n) ∈ S ↔ hasOrigin = true := by
  classical
  rcases
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_mem_iff.mp
        hS with
    ⟨R, hRpow, _hRcard, hSR⟩
  have horigin_ne_v : IsingFK.boxOrigin 3 n ≠ v :=
    boxOrigin_ne_of_boxBoundary 3 n (Finset.mem_filter.mp hv).2
  constructor
  · intro horiginS
    have horiginUnion :
        some (IsingFK.boxOrigin 3 n) ∈
          finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R := by
      simpa [hSR] using horiginS
    rcases Finset.mem_union.mp horiginUnion with hmarked | hR
    · rcases
        finiteBoundaryGhostSourceClassEndpointMarkedSources_mem_iff.mp
          hmarked with
        hghost | horigin | hendpoint
      · simp at hghost
      · exact horigin.2
      · have h : IsingFK.boxOrigin 3 n = v := by
          simpa using Option.some.inj hendpoint.1
        exact False.elim (horigin_ne_v h)
    · have hUnmarked :
          some (IsingFK.boxOrigin 3 n) ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v :=
        (Finset.mem_powerset.mp hRpow) hR
      exact False.elim
        ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_mem_iff.mp
          hUnmarked).2.1 rfl)
  · intro horigin
    have hmarked :
        some (IsingFK.boxOrigin 3 n) ∈
          finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint :=
      finiteBoundaryGhostSourceClassEndpointMarkedSources_mem_iff.mpr
        (Or.inr (Or.inl ⟨rfl, horigin⟩))
    have horiginUnion :
        some (IsingFK.boxOrigin 3 n) ∈
          finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R :=
      Finset.mem_union.mpr (Or.inl hmarked)
    simpa [hSR] using horiginUnion

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_endpoint_mem_iff_of_boundary
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
          v hasGhost hasOrigin hasEndpoint k) :
    some v ∈ S ↔ hasEndpoint = true := by
  classical
  rcases
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_mem_iff.mp
        hS with
    ⟨R, hRpow, _hRcard, hSR⟩
  have horigin_ne_v : IsingFK.boxOrigin 3 n ≠ v :=
    boxOrigin_ne_of_boxBoundary 3 n (Finset.mem_filter.mp hv).2
  constructor
  · intro hendpointS
    have hendpointUnion :
        some v ∈
          finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R := by
      simpa [hSR] using hendpointS
    rcases Finset.mem_union.mp hendpointUnion with hmarked | hR
    · rcases
        finiteBoundaryGhostSourceClassEndpointMarkedSources_mem_iff.mp
          hmarked with
        hghost | horigin | hendpoint
      · simp at hghost
      · have h : IsingFK.boxOrigin 3 n = v := by
          exact (Option.some.inj horigin.1).symm
        exact False.elim (horigin_ne_v h)
      · exact hendpoint.2
    · have hUnmarked :
          some v ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v :=
        (Finset.mem_powerset.mp hRpow) hR
      exact False.elim
        ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_mem_iff.mp
          hUnmarked).2.2 rfl)
  · intro hendpoint
    have hmarked :
        some v ∈ finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint :=
      finiteBoundaryGhostSourceClassEndpointMarkedSources_mem_iff.mpr
        (Or.inr (Or.inr ⟨rfl, hendpoint⟩))
    have hendpointUnion :
        some v ∈
          finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R :=
      Finset.mem_union.mpr (Or.inl hmarked)
    simpa [hSR] using hendpointUnion

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_card_ge_four_of_boundary_of_mem_shellIndex
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (hk :
      k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint)
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
          v hasGhost hasOrigin hasEndpoint k) :
    4 ≤ S.card := by
  classical
  have hkthreshold :
      finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
        hasGhost hasOrigin hasEndpoint ≤ k :=
    by
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
      exact (Finset.mem_filter.mp hkfilter).2
  have hthreshold :=
    finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_add_markedSources_card_eq_four_of_boundary
      hv hasGhost hasOrigin hasEndpoint
  have hcard :=
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_card_eq
      hS
  omega

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_membershipCase_eq_label_of_boundary_of_mem_shellIndex
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (hk :
      k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint)
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
          v hasGhost hasOrigin hasEndpoint k) :
    finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
      finiteBoundaryGhostSourceClassEndpointMembershipLabel
        SourceClassCardinalityCase.fourPlus
        hasGhost hasOrigin hasEndpoint := by
  classical
  have hfour :
      4 ≤ S.card :=
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_card_ge_four_of_boundary_of_mem_shellIndex
      hv hk hS
  have hcardCase :
      finiteBoundaryGhostSourceClassCardinalityCase S =
        SourceClassCardinalityCase.fourPlus := by
    unfold finiteBoundaryGhostSourceClassCardinalityCase
    have hnotZero : ¬ S.card = 0 := by omega
    have hnotTwo : ¬ S.card = 2 := by omega
    simp [hnotZero, hnotTwo]
  have hghostIff :
      none ∈ S ↔ hasGhost = true :=
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_ghost_mem_iff
      hS
  have horiginIff :
      some (IsingFK.boxOrigin 3 n) ∈ S ↔ hasOrigin = true :=
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_origin_mem_iff_of_boundary
      hv hS
  have hendpointIff :
      some v ∈ S ↔ hasEndpoint = true :=
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_endpoint_mem_iff_of_boundary
      hv hS
  have hghost : decide (none ∈ S) = hasGhost := by
    cases hasGhost <;> simp [hghostIff]
  have horigin :
      decide (some (IsingFK.boxOrigin 3 n) ∈ S) = hasOrigin := by
    cases hasOrigin <;> simp [horiginIff]
  have hendpoint : decide (some v ∈ S) = hasEndpoint := by
    cases hasEndpoint <;> simp [hendpointIff]
  simp [
    finiteBoundaryGhostSourceClassEndpointMembershipCase,
    finiteBoundaryGhostSourceClassEndpointMembershipLabel,
    hcardCase, hghost, horigin, hendpoint]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk :
      k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k =
      ∑ S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                finiteBoundaryGhostSourceClassEndpointMembershipLabel
                  SourceClassCardinalityCase.fourPlus
                  hasGhost hasOrigin hasEndpoint ∧
              (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
                k),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
  classical
  let exactImage :=
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
      v hasGhost hasOrigin hasEndpoint k
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ω v
  let label :=
    finiteBoundaryGhostSourceClassEndpointMembershipLabel
      SourceClassCardinalityCase.fourPlus
      hasGhost hasOrigin hasEndpoint
  have hfilter :
      exactImage.filter (fun S => S ∈ sourceClassSupport) =
        sourceClassSupport.filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                label ∧
              (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
                k) := by
    ext S
    constructor
    · intro hS
      rcases Finset.mem_filter.mp hS with ⟨hSimage, hSsupport⟩
      have hcase :
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            label := by
        simpa [exactImage, label] using
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_membershipCase_eq_label_of_boundary_of_mem_shellIndex
            hv hk hSimage
      have hres :
          (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
            k := by
        simpa [exactImage] using
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_unmarkedResidual_card_eq
            hSimage
      exact Finset.mem_filter.mpr ⟨hSsupport, hcase, hres⟩
    · intro hS
      rcases Finset.mem_filter.mp hS with
        ⟨hSsupport, hcase, hres⟩
      have hSimage :
          S ∈ exactImage := by
        simpa [exactImage, label] using
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_fourPlus_unmarkedResidualCard_subset_markedResidualExactCardImage
            n Ω v hasGhost hasOrigin hasEndpoint k
            (Finset.mem_filter.mpr ⟨hSsupport, hcase, hres⟩)
      exact Finset.mem_filter.mpr ⟨hSimage, hSsupport⟩
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
  calc
    (∑ S ∈ exactImage,
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S)
        =
      ∑ S ∈ exactImage.filter (fun S => S ∈ sourceClassSupport),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
        symm
        exact Finset.sum_subset
          (by
            intro S hS
            exact (Finset.mem_filter.mp hS).1)
          (by
            intro S hSimage hSnotFilter
            have hSnotSupport : S ∉ sourceClassSupport := by
              intro hSsupport
              exact hSnotFilter
                (Finset.mem_filter.mpr ⟨hSimage, hSsupport⟩)
            exact
              finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_eq_zero_of_not_mem_sourceClassSupport
                β H hSnotSupport)
    _ =
      ∑ S ∈
        sourceClassSupport.filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                label ∧
              (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
                k),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
        rw [hfilter]
    _ =
      ∑ S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                finiteBoundaryGhostSourceClassEndpointMembershipLabel
                  SourceClassCardinalityCase.fourPlus
                  hasGhost hasOrigin hasEndpoint ∧
              (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
                k),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
        rfl

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_true_true_true_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_Icc_one
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {k : ℕ}
    (hk : k ∈ Finset.Icc 1 ((2 * n + 1) ^ 3 - 2)) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v true true true k =
      ∑ S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                finiteBoundaryGhostSourceClassEndpointMembershipLabel
                  SourceClassCardinalityCase.fourPlus
                  true true true ∧
              (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
                k),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
  have hkShell :
      k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v true true true := by
    simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_true_true_true_eq_Icc_box_volume_sub_two_of_boundary
        hv] using hk
  exact
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
      β H n Ω v hv true true true hkShell

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_sum_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint =
      ∑ S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
              finiteBoundaryGhostSourceClassEndpointMembershipLabel
                SourceClassCardinalityCase.fourPlus
                hasGhost hasOrigin hasEndpoint),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
  classical
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_unmarkedResidualCard_shell_sum
      β H n Ω v hv hasGhost hasOrigin hasEndpoint]
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
  apply Finset.sum_congr rfl
  intro k hk
  simpa [Finset.filter_filter, and_assoc] using
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
      β H n Ω v hv hasGhost hasOrigin hasEndpoint hk

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_zero_of_boundary_of_shellIndex_eq_empty
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool)
    (hidx :
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint =
        ∅) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              hasGhost hasOrigin hasEndpoint),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      0 := by
  rw [
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_fourPlus_eq_empty_of_boundary_of_shellIndex_eq_empty
      hv hasGhost hasOrigin hasEndpoint hidx]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_zero_of_boundary_of_box_volume_sub_two_lt_threshold
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool)
    (hcard :
      (2 * n + 1) ^ 3 - 2 <
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              hasGhost hasOrigin hasEndpoint),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      0 := by
  exact
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_zero_of_boundary_of_shellIndex_eq_empty
      β H n Ω hv hasGhost hasOrigin hasEndpoint
      ((finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_eq_empty_iff_box_volume_sub_two_of_boundary
        hv hasGhost hasOrigin hasEndpoint).mpr hcard)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              hasGhost hasOrigin hasEndpoint),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      ∑ k ∈
        Finset.Icc
          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint)
          ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint k := by
  calc
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              hasGhost hasOrigin hasEndpoint),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S)
        =
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint := by
        symm
        exact
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_sum_of_boundary
            β H n Ω v hv hasGhost hasOrigin hasEndpoint
    _ =
      ∑ k ∈
        Finset.Icc
          (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint)
          ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint k := by
        exact
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
            β H n Ω hv hasGhost hasOrigin hasEndpoint

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_false_false_false_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              false false false),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      ∑ k ∈ Finset.Icc 4 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v false false false k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv false false false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_false_false_true_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              false false true),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v false false true k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv false false true

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_false_true_false_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              false true false),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v false true false k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv false true false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_false_true_true_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              false true true),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v false true true k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv false true true

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_true_false_false_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              true false false),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v true false false k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv true false false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_true_false_true_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              true false true),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v true false true k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv true false true

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_true_true_false_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              true true false),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v true true false k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv true true false

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_true_true_true_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              true true true),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      ∑ k ∈ Finset.Icc 1 ((2 * n + 1) ^ 3 - 2),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v true true true k := by
  simpa [finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold] using
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_eq_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
      β H n Ω hv true true true

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_true_true_true_eq_even_filter_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              true true true),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) =
      ∑ k ∈
        (Finset.Icc 1 ((2 * n + 1) ^ 3 - 2)).filter
          (fun k => Even (1 + k)),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v true true true k := by
  calc
    (∑ S ∈
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
        n Ω v).filter
        (fun S =>
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
            finiteBoundaryGhostSourceClassEndpointMembershipLabel
              SourceClassCardinalityCase.fourPlus
              true true true),
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S)
        =
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v true true true := by
        symm
        exact
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_sum_of_boundary
            β H n Ω v hv true true true
    _ =
      ∑ k ∈
        (Finset.Icc 1 ((2 * n + 1) ^ 3 - 2)).filter
          (fun k => Even (1 + k)),
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v true true true k := by
        exact
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_true_true_true_eq_even_filter_sum_Icc_exactCardImageSourceClassSum_box_volume_sub_two_of_boundary
            β H n Ω hv

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMarkedSources_union_left_cancel_of_unmarked_powerset
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R R' : Finset (Option (FK.boxVerts 3 n))}
    (hR :
      R ∈ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset)
    (hR' :
      R' ∈ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset)
    (hunion :
      finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R =
        finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R') :
    R = R' := by
  classical
  ext x
  constructor
  · intro hxR
    have hxUnion :
        x ∈ finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R' := by
      have hx :
          x ∈ finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R :=
        Finset.mem_union.mpr (Or.inr hxR)
      simpa [hunion] using hx
    rcases Finset.mem_union.mp hxUnion with hxMarked | hxR'
    · have hxU : x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v :=
        (Finset.mem_powerset.mp hR) hxR
      have hxnotU :=
        (Finset.disjoint_left.mp
          (finiteBoundaryGhostSourceClassEndpointMarkedSources_disjoint_unmarkedOptions
            v hasGhost hasOrigin hasEndpoint)) hxMarked
      exact False.elim (hxnotU hxU)
    · exact hxR'
  · intro hxR'
    have hxUnion :
        x ∈ finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R := by
      have hx :
          x ∈ finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R' :=
        Finset.mem_union.mpr (Or.inr hxR')
      simpa [hunion] using hx
    rcases Finset.mem_union.mp hxUnion with hxMarked | hxR
    · have hxU : x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v :=
        (Finset.mem_powerset.mp hR') hxR'
      have hxnotU :=
        (Finset.disjoint_left.mp
          (finiteBoundaryGhostSourceClassEndpointMarkedSources_disjoint_unmarkedOptions
            v hasGhost hasOrigin hasEndpoint)) hxMarked
      exact False.elim (hxnotU hxU)
    · exact hxR

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_eq_image_unmarkedResidualExactCardSet
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
        v hasGhost hasOrigin hasEndpoint k =
      (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k).image
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R) := by
  rfl

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_le_unmarkedResidualExactCardSet_card
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) :
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint k).card ≤
      (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k).card := by
  classical
  have hsubset :
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
          n Ω v hasGhost hasOrigin hasEndpoint k ⊆
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
          v hasGhost hasOrigin hasEndpoint k := by
    simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_filter_endpointMembership_fourPlus_unmarkedResidualCard_subset_markedResidualExactCardImage
          n Ω v hasGhost hasOrigin hasEndpoint k
  have hsupportImage :
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
          n Ω v hasGhost hasOrigin hasEndpoint k).card ≤
        (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
          v hasGhost hasOrigin hasEndpoint k).card :=
    Finset.card_le_card hsubset
  have himageDomain :
      (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
          v hasGhost hasOrigin hasEndpoint k).card ≤
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k).card := by
    rw [
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_eq_image_unmarkedResidualExactCardSet]
    exact Finset.card_image_le
  exact hsupportImage.trans himageDomain

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_le_nonemptyResidualCaseSet_card
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) :
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint k).card ≤
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet
        v Ω hasGhost hasOrigin hasEndpoint k).card := by
  classical
  let sourceSet :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
      n Ω v hasGhost hasOrigin hasEndpoint k
  let residualMap : Finset (Option (FK.boxVerts 3 n)) →
      Finset (Option (FK.boxVerts 3 n)) :=
    fun S => finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S
  have hinj : Set.InjOn residualMap (sourceSet : Set (Finset (Option (FK.boxVerts 3 n)))) := by
    intro S hS T hT hres
    have hcaseS :
        finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
          finiteBoundaryGhostSourceClassEndpointMembershipLabel
            SourceClassCardinalityCase.fourPlus
            hasGhost hasOrigin hasEndpoint :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_mem_iff.mp
        (by simpa [sourceSet] using hS)).2.1
    have hcaseT :
        finiteBoundaryGhostSourceClassEndpointMembershipCase v T =
          finiteBoundaryGhostSourceClassEndpointMembershipLabel
            SourceClassCardinalityCase.fourPlus
            hasGhost hasOrigin hasEndpoint :=
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_mem_iff.mp
        (by simpa [sourceSet] using hT)).2.1
    have hdecompS :
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S =
            S :=
      finiteBoundaryGhostSourceClassEndpointMarkedSources_union_unmarkedResidual_eq_of_endpointMembershipCase_eq_label
        hcaseS
    have hdecompT :
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v T =
            T :=
      finiteBoundaryGhostSourceClassEndpointMarkedSources_union_unmarkedResidual_eq_of_endpointMembershipCase_eq_label
        hcaseT
    calc
      S =
          finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S := hdecompS.symm
      _ =
          finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v T := by
            simpa [residualMap] using congrArg
              (fun R =>
                finiteBoundaryGhostSourceClassEndpointMarkedSources
                  v hasGhost hasOrigin hasEndpoint ∪ R) hres
      _ = T := hdecompT
  have hcardImage :
      sourceSet.card = (sourceSet.image residualMap).card := by
    exact (Finset.card_image_of_injOn (s := sourceSet) (f := residualMap) hinj).symm
  have hsubset :
      sourceSet.image residualMap ⊆
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet
          v Ω hasGhost hasOrigin hasEndpoint k := by
    intro R hR
    rcases Finset.mem_image.mp hR with ⟨S, hS, rfl⟩
    have hSmem :
        S ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
            n Ω v hasGhost hasOrigin hasEndpoint k := by
      simpa [sourceSet] using hS
    rcases
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_mem_iff.mp
        hSmem with
      ⟨hSsupport, hcase, hcard⟩
    have hdecomp :
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S =
            S :=
      finiteBoundaryGhostSourceClassEndpointMarkedSources_union_unmarkedResidual_eq_of_endpointMembershipCase_eq_label
        hcase
    refine
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet_mem_iff.mpr
        ⟨?_, ?_⟩
    · exact
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_mem_iff.mpr
          ⟨Finset.mem_powerset.mp
              (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_powerset
                v S),
            hcard⟩
    · rcases Finset.mem_image.mp hSsupport with ⟨E, hE, hEsource⟩
      refine ⟨E, ?_⟩
      exact
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet_mem_iff.mpr
          ⟨hE, hEsource.trans hdecomp.symm⟩
  calc
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint k).card = sourceSet.card := by
        rfl
    _ = (sourceSet.image residualMap).card := hcardImage
    _ ≤
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet
          v Ω hasGhost hasOrigin hasEndpoint k).card :=
        Finset.card_le_card hsubset

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet_card_le_sum_residualCaseClassifiedSet_card
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) :
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet
        v Ω hasGhost hasOrigin hasEndpoint k).card ≤
      ∑ R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R).card := by
  classical
  let nonemptyCases :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet
      v Ω hasGhost hasOrigin hasEndpoint k
  let exactCases :=
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v k
  let classifiedCount : Finset (Option (FK.boxVerts 3 n)) → ℕ :=
    fun R =>
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
        v Ω hasGhost hasOrigin hasEndpoint R).card
  have hsubset : nonemptyCases ⊆ exactCases := by
    intro R hR
    exact
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet_mem_iff.mp
        (by simpa [nonemptyCases] using hR)).1
  calc
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet
        v Ω hasGhost hasOrigin hasEndpoint k).card = nonemptyCases.card := by
        rfl
    _ = ∑ R ∈ nonemptyCases, 1 := Finset.card_eq_sum_ones nonemptyCases
    _ ≤ ∑ R ∈ nonemptyCases, classifiedCount R := by
        exact Finset.sum_le_sum fun R hR => by
          have hnonempty :
              (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                v Ω hasGhost hasOrigin hasEndpoint R).Nonempty :=
            (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet_mem_iff.mp
              (by simpa [nonemptyCases] using hR)).2
          exact Finset.one_le_card.mpr hnonempty
    _ ≤ ∑ R ∈ exactCases, classifiedCount R := by
        exact
          Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun R _hRexact _hRnot => Nat.zero_le (classifiedCount R))
    _ =
      ∑ R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R).card := by
        rfl

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_le_sum_residualCaseClassifiedSet_card
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) :
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint k).card ≤
      ∑ R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R).card :=
  (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_le_nonemptyResidualCaseSet_card
      Ω v hasGhost hasOrigin hasEndpoint k).trans
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardNonemptyResidualCaseSet_card_le_sum_residualCaseClassifiedSet_card
      Ω v hasGhost hasOrigin hasEndpoint k)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_cast_le_sum_residualCaseClassifiedSet_card
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) :
    ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint k).card : ℝ) ≤
      ∑ R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R).card : ℝ) := by
  exact_mod_cast
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_le_sum_residualCaseClassifiedSet_card
      Ω v hasGhost hasOrigin hasEndpoint k

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_one_le_sum_singleton_residualCaseClassifiedSet_card
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint 1).card ≤
      ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint
          ({x} : Finset (Option (FK.boxVerts 3 n)))).card := by
  have h :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_le_sum_residualCaseClassifiedSet_card
      Ω v hasGhost hasOrigin hasEndpoint 1
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_one_sum_eq_unmarkedOptions_singleton_sum
      v
      (fun R =>
        (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R).card)] at h
  exact h

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_one_cast_le_sum_singleton_residualCaseClassifiedSet_card
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint 1).card : ℝ) ≤
      ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
        ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint
          ({x} : Finset (Option (FK.boxVerts 3 n)))).card : ℝ) := by
  have h :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_cast_le_sum_residualCaseClassifiedSet_card
      Ω v hasGhost hasOrigin hasEndpoint 1
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_one_sum_eq_unmarkedOptions_singleton_sum
      v
      (fun R =>
        ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R).card : ℝ))] at h
  exact h

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_le_unmarkedOptions_card_one
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint 1).card ≤
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card := by
  calc
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint 1).card ≤
      (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v 1).card :=
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_le_unmarkedResidualExactCardSet_card
          Ω v hasGhost hasOrigin hasEndpoint 1
    _ = (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card := by
      rw [
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_card_eq_choose]
      simp

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_le_box_volume_sub_two_of_boundary
    {n : ℕ}
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint 1).card ≤
      ((2 * n + 1) ^ 3 - 2) := by
  have hcount :
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
          n Ω v hasGhost hasOrigin hasEndpoint 1).card ≤
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_le_unmarkedOptions_card_one
      Ω v hasGhost hasOrigin hasEndpoint
  simpa [
    finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_box_volume_sub_two_of_boundary
      hv] using hcount

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_zero_eq_singleton_markedSources
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
        v hasGhost hasOrigin hasEndpoint 0 =
      ({finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint} :
        Finset (Finset (Option (FK.boxVerts 3 n)))) := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_eq_image_unmarkedResidualExactCardSet,
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_zero_eq_singleton_empty]
  ext S
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_eq_empty_of_unmarkedOptions_card_lt
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk :
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card < k) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
        v hasGhost hasOrigin hasEndpoint k =
      ∅ := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_eq_image_unmarkedResidualExactCardSet,
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_eq_empty_iff.mpr
      hk]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_eq_empty_of_boundary_of_box_volume_sub_two_lt
    {n : ℕ} {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk : (2 * n + 1) ^ 3 - 2 < k) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
        v hasGhost hasOrigin hasEndpoint k =
      ∅ :=
  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_eq_empty_of_unmarkedOptions_card_lt
    hasGhost hasOrigin hasEndpoint
    (by
      rw [
        finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
          hv,
        StatMech.FK.ecz_boxVerts_card]
      exact hk)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_mem_iff_unmarkedResidualExactCardSet
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    {S : Finset (Option (FK.boxVerts 3 n))} :
    S ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
          v hasGhost hasOrigin hasEndpoint k ↔
      ∃ R,
        R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k ∧
          finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R =
            S := by
  classical
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_eq_image_unmarkedResidualExactCardSet]
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨R, hR, hSR⟩
    exact ⟨R, hR, hSR⟩
  · rintro ⟨R, hR, hSR⟩
    exact Finset.mem_image.mpr ⟨R, hR, hSR⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_union_mem_of_unmarkedResidualExactCardSet
    {n : ℕ} {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    {R : Finset (Option (FK.boxVerts 3 n))}
    (hR :
      R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k) :
    finiteBoundaryGhostSourceClassEndpointMarkedSources
        v hasGhost hasOrigin hasEndpoint ∪ R ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
        v hasGhost hasOrigin hasEndpoint k :=
  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_mem_iff_unmarkedResidualExactCardSet.mpr
    ⟨R, hR, rfl⟩

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_unmarkedResidualExactCardSet_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k =
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v k,
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R) := by
  classical
  unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_eq_image_unmarkedResidualExactCardSet]
  rw [Finset.sum_image]
  intro R hR R' hR' hunion
  exact
    finiteBoundaryGhostSourceClassEndpointMarkedSources_union_left_cancel_of_unmarked_powerset
      (Finset.mem_powerset.mpr
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_mem_iff.mp
          hR).1)
      (Finset.mem_powerset.mpr
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_mem_iff.mp
          hR').1)
      hunion

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_zero_eq_markedSources
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint 0 =
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v
        (finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint) := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_unmarkedResidualExactCardSet_sum,
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_zero_sum_eq_empty]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_zero_of_unmarkedOptions_card_lt
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk :
      (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card < k) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k =
      0 := by
  unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_eq_empty_of_unmarkedOptions_card_lt
      hasGhost hasOrigin hasEndpoint hk]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_zero_of_boundary_of_box_volume_sub_two_lt
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk : (2 * n + 1) ^ 3 - 2 < k) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k =
      0 :=
  finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_zero_of_unmarkedOptions_card_lt
    β H n Ω v hasGhost hasOrigin hasEndpoint
    (by
      rw [
        finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_card_eq_boxVerts_card_sub_two_of_boundary
          hv,
        StatMech.FK.ecz_boxVerts_card]
      exact hk)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_one_eq_unmarkedOptions_singleton_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint 1 =
      ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))) := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_unmarkedResidualExactCardSet_sum]
  exact
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_one_sum_eq_unmarkedOptions_singleton_sum
      v
      (fun R =>
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R))

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_eq_empty_of_boundary_of_threshold_add_k_odd
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hodd :
      Odd
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint +
          k)) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint k =
      ∅ := by
  classical
  ext S
  constructor
  · intro hS
    exfalso
    rcases
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_mem_iff.mp
          hS with
      ⟨hSsupport, hcase, hresCard⟩
    have hEven :
        Even S.card :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_card_even
        hSsupport
    let R := finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S
    have hRpow :
        R ∈ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset := by
      simpa [R] using
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_powerset v S
    have hunion :
        finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R =
          S := by
      simpa [R] using
        finiteBoundaryGhostSourceClassEndpointMarkedSources_union_unmarkedResidual_eq_of_endpointMembershipCase_eq_label
          hcase
    have hcardUnion :
        (finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R).card =
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint).card + R.card :=
      finiteBoundaryGhostSourceClassEndpointMarkedSources_union_card_eq
        v hasGhost hasOrigin hasEndpoint hRpow
    have hcard :
        S.card =
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint).card + k := by
      rw [← hunion]
      simpa [R, hresCard] using hcardUnion
    have hthreshold :
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint +
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint).card =
          4 :=
      finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_add_markedSources_card_eq_four_of_boundary
        hv hasGhost hasOrigin hasEndpoint
    rw [hcard] at hEven
    rcases hEven with ⟨a, ha⟩
    rcases hodd with ⟨b, hb⟩
    omega
  · intro hS
    simp at hS

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_eq_zero_of_boundary_of_threshold_add_k_odd
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hodd :
      Odd
        (finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint +
          k)) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k =
      0 := by
  unfold finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_eq_empty_of_boundary_of_threshold_add_k_odd
      hv hasGhost hasOrigin hasEndpoint hodd]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_eq_empty_of_boundary_of_lt_threshold
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk :
      k <
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint k =
      ∅ := by
  classical
  ext S
  constructor
  · intro hS
    rcases
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_mem_iff.mp
          hS with
      ⟨hSsupport, hcase, hresCard⟩
    have hSfilter :
        S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter
            (fun S =>
              finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                finiteBoundaryGhostSourceClassEndpointMembershipLabel
                  SourceClassCardinalityCase.fourPlus
                  hasGhost hasOrigin hasEndpoint) :=
      Finset.mem_filter.mpr ⟨hSsupport, hcase⟩
    have hkShell :
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card ∈
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
            v hasGhost hasOrigin hasEndpoint :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_mem_thresholdShellIndex_of_mem
        hv hSfilter
    have hthresholdLe :
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint ≤
          (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card :=
      (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff.mp
        hkShell).1
    omega
  · intro hS
    simp at hS

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_eq_zero_of_boundary_of_lt_threshold
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk :
      k <
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k =
      0 := by
  unfold finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_eq_empty_of_boundary_of_lt_threshold
      hv hasGhost hasOrigin hasEndpoint hk]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_zero_eq_empty_of_boundary
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint 0 =
      ∅ := by
  classical
  ext S
  constructor
  · intro hS
    rcases
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_mem_iff.mp
          hS with
      ⟨hSsupport, hcase, hresCard⟩
    have hSfilter :
        S ∈
          (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
            n Ω v).filter
            (fun S =>
              finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                finiteBoundaryGhostSourceClassEndpointMembershipLabel
                  SourceClassCardinalityCase.fourPlus
                  hasGhost hasOrigin hasEndpoint) :=
      Finset.mem_filter.mpr ⟨hSsupport, hcase⟩
    have hkShell :
        (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card ∈
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
            v hasGhost hasOrigin hasEndpoint :=
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_mem_thresholdShellIndex_of_mem
        hv hSfilter
    have hthresholdLe :
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint ≤
          (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card :=
      (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff.mp
        hkShell).1
    have hthresholdPos :
        0 <
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint :=
      finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold_pos
        hasGhost hasOrigin hasEndpoint
    omega
  · intro hS
    simp at hS

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_zero_eq_zero_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint 0 =
      0 := by
  unfold finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_zero_eq_empty_of_boundary
      hv hasGhost hasOrigin hasEndpoint]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_eq_empty_of_boundary_of_not_mem_shellIndex
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk :
      k ∉
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ω v hasGhost hasOrigin hasEndpoint k =
      ∅ := by
  by_cases hlow :
      k <
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint
  · exact
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_eq_empty_of_boundary_of_lt_threshold
        hv hasGhost hasOrigin hasEndpoint hlow
  · have hthreshold :
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint ≤
          k := Nat.le_of_not_lt hlow
    by_cases hupper : k ≤ (2 * n + 1) ^ 3 - 2
    · have hkShell :
          k ∈
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
              v hasGhost hasOrigin hasEndpoint := by
        rw [
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex_mem_iff_box_volume_sub_two_of_boundary
            hv]
        exact ⟨hthreshold, hupper⟩
      exact False.elim (hk hkShell)
    · have hvol_lt : (2 * n + 1) ^ 3 - 2 < k :=
        Nat.lt_of_not_ge hupper
      exact
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_eq_empty_of_boundary_of_box_volume_sub_two_lt
          hv hasGhost hasOrigin hasEndpoint hvol_lt

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_eq_zero_of_boundary_of_not_mem_shellIndex
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk :
      k ∉
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k =
      0 := by
  unfold finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_eq_empty_of_boundary_of_not_mem_shellIndex
      hv hasGhost hasOrigin hasEndpoint hk]
  simp

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_eq_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) {k : ℕ}
    (hk :
      k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k =
      ∑ R ∈
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
          (fun R => R.card = k),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R) := by
  classical
  have himage :
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint k =
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint k := by
    simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum,
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
          β H n Ω v hv hasGhost hasOrigin hasEndpoint hk
  calc
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k
        =
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k := himage.symm
    _ =
      ∑ R ∈
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
          (fun R => R.card = k),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R) := by
        unfold
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
        rw [Finset.sum_image]
        intro R hR R' hR' hunion
        exact
          finiteBoundaryGhostSourceClassEndpointMarkedSources_union_left_cancel_of_unmarked_powerset
            (Finset.mem_filter.mp hR).1
            (Finset.mem_filter.mp hR').1
            hunion

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_one_eq_unmarkedOptions_singleton_sum_of_boundary_of_mem_shellIndex
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool)
    (hk :
      1 ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint 1 =
      ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))) := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_eq_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
      β H n Ω v hv hasGhost hasOrigin hasEndpoint hk]
  simpa [finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet] using
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_one_sum_eq_unmarkedOptions_singleton_sum
      v
      (fun R =>
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R))

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_le_unmarkedResidualCaseShareMul_of_boundary_of_mem_shellIndex
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (hk :
      k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint)
    {residualShare : Finset (Option (FK.boxVerts 3 n)) → ℝ}
    (hR :
      ∀ R, R ∈
          (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
            (fun R => R.card = k) →
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R) ≤
          residualShare R * D) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint k ≤
      (∑ R ∈
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
          (fun R => R.card = k),
        residualShare R) * D := by
  classical
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_eq_unmarkedResidualCard_sum_of_boundary_of_mem_shellIndex
      β H n Ω v hv hasGhost hasOrigin hasEndpoint hk]
  calc
    (∑ R ∈
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
          (fun R => R.card = k),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R))
        ≤
      ∑ R ∈
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
          (fun R => R.card = k),
        residualShare R * D := by
        exact Finset.sum_le_sum (fun R hRmem => hR R hRmem)
    _ =
      (∑ R ∈
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
          (fun R => R.card = k),
        residualShare R) * D := by
        exact
          (Finset.sum_mul
            ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
              (fun R => R.card = k))
            residualShare D).symm

set_option linter.style.longLine false in


theorem sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_unmarkedResidualCaseShares
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (hk :
      k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint)
    {residualShare : Finset (Option (FK.boxVerts 3 n)) → ℝ}
    (hshare :
      0 ≤
        ∑ R ∈
          (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
            (fun R => R.card = k),
          residualShare R)
    (hR :
      ∀ R, R ∈
          (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
            (fun R => R.card = k) →
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R) ≤
          residualShare R * D) :
    SourceClassEndpointMembershipSupportResidualExactCardShellCellShare
      v β H Ω hasGhost hasOrigin hasEndpoint k
      (∑ R ∈
        (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
          (fun R => R.card = k),
        residualShare R)
      D := by
  exact
    ⟨hshare,
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum_le_unmarkedResidualCaseShareMul_of_boundary_of_mem_shellIndex
        hv hk hR⟩

set_option linter.style.longLine false in


theorem sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_residualCaseShares
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (hk :
      k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint)
    {residualShare : Finset (Option (FK.boxVerts 3 n)) → ℝ}
    (hR :
      ∀ R, R ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k →
        SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
          v β H Ω hasGhost hasOrigin hasEndpoint R (residualShare R) D) :
    SourceClassEndpointMembershipSupportResidualExactCardShellCellShare
      v β H Ω hasGhost hasOrigin hasEndpoint k
      (∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v k,
        residualShare R)
      D := by
  classical
  have hshare :
      0 ≤
        ∑ R ∈
          (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
            (fun R => R.card = k),
          residualShare R := by
    exact Finset.sum_nonneg
      (fun R hRmem =>
        (hR R (by
          simpa [finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet]
            using hRmem)).1)
  have hbound :
      ∀ R, R ∈
          (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
            (fun R => R.card = k) →
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R) ≤
          residualShare R * D := by
    intro R hRmem
    exact
      (hR R (by
        simpa [finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet]
          using hRmem)).2
  simpa [finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet]
    using
      sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_unmarkedResidualCaseShares
        hv hk hshare hbound

set_option linter.style.longLine false in


theorem sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_residualCaseLabelShares
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (hk :
      k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {label :
      Finset (Option (FK.boxVerts 3 n)) →
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι}
    {labelShare : Finset (Option (FK.boxVerts 3 n)) → ι → ℝ}
    (hR :
      ∀ R, R ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k →
        SourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare
          v β H Ω hasGhost hasOrigin hasEndpoint R (label R)
          (labelShare R) D) :
    SourceClassEndpointMembershipSupportResidualExactCardShellCellShare
      v β H Ω hasGhost hasOrigin hasEndpoint k
      (∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v k,
        ∑ i : ι, labelShare R i)
      D := by
  classical
  exact
    sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_residualCaseShares
      (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
      hv hk
      (residualShare := fun R => ∑ i : ι, labelShare R i)
      (fun R hRmem =>
        sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
          (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
          (hasGhost := hasGhost) (hasOrigin := hasOrigin)
          (hasEndpoint := hasEndpoint) (R := R)
          (label := label R) (labelShare := labelShare R)
          (hR R hRmem))

set_option linter.style.longLine false in


theorem sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_residualCaseDependentLabelShares
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {hasGhost hasOrigin hasEndpoint : Bool} {k : ℕ}
    (hk :
      k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v hasGhost hasOrigin hasEndpoint)
    {ι : Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ R, Fintype (ι R)] [∀ R, DecidableEq (ι R)]
    {label :
      ∀ R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι R}
    {labelShare : ∀ R, ι R → ℝ}
    (hR :
      ∀ R, R ∈
          finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
            v k →
        SourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare
          v β H Ω hasGhost hasOrigin hasEndpoint R (label R)
          (labelShare R) D) :
    SourceClassEndpointMembershipSupportResidualExactCardShellCellShare
      v β H Ω hasGhost hasOrigin hasEndpoint k
      (∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v k,
        ∑ i : ι R, labelShare R i)
      D := by
  classical
  exact
    sourceClassEndpointMembershipSupportResidualExactCardShellCellShare_of_residualCaseShares
      (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
      hv hk
      (residualShare := fun R => ∑ i : ι R, labelShare R i)
      (fun R hRmem =>
        sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
          (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
          (hasGhost := hasGhost) (hasOrigin := hasOrigin)
          (hasEndpoint := hasEndpoint) (R := R)
          (ι := ι R) (label := label R) (labelShare := labelShare R)
          (hR R hRmem))

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_pairwiseDisjoint
    {n : ℕ} (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    (((Finset.range
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card + 1)).filter
      (fun k =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ k) : Finset ℕ) :
        Set ℕ).PairwiseDisjoint
      (fun k =>
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
          v hasGhost hasOrigin hasEndpoint k) := by
  classical
  intro k _hk l _hl hkl
  change Disjoint
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
      v hasGhost hasOrigin hasEndpoint k)
    (finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
      v hasGhost hasOrigin hasEndpoint l)
  rw [Finset.disjoint_left]
  intro S hSk hSl
  rcases Finset.mem_image.mp hSk with ⟨R, hRfilter, hSR⟩
  rcases Finset.mem_image.mp hSl with ⟨R', hR'filter, hSR'⟩
  have hRpow :
      R ∈ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset :=
    (Finset.mem_filter.mp hRfilter).1
  have hR'pow :
      R' ∈ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset :=
    (Finset.mem_filter.mp hR'filter).1
  have hRcard : R.card = k := (Finset.mem_filter.mp hRfilter).2
  have hR'card : R'.card = l := (Finset.mem_filter.mp hR'filter).2
  have hunion :
      finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R =
        finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R' := by
    exact hSR.trans hSR'.symm
  have hRR' : R = R' :=
    finiteBoundaryGhostSourceClassEndpointMarkedSources_union_left_cancel_of_unmarked_powerset
      hRpow hR'pow hunion
  have hkeq : k = l := by
    calc
      k = R.card := hRcard.symm
      _ = R'.card := by rw [hRR']
      _ = l := hR'card
  exact hkl hkeq

set_option linter.style.longLine false in
set_option maxHeartbeats 800000 in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint ≤
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint := by
  classical
  let K :=
    (Finset.range
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card + 1)).filter
      (fun k =>
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ k)
  have hsubset :
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset.filter
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
            hasGhost hasOrigin hasEndpoint ≤ R.card)).image
        (fun R =>
          finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R) ⊆
        K.biUnion
          (fun k =>
            finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
              v hasGhost hasOrigin hasEndpoint k) := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨R, hRfilter, hSR⟩
    have hRpow :
        R ∈ (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).powerset :=
      (Finset.mem_filter.mp hRfilter).1
    have hRthreshold :
        finiteBoundaryGhostSourceClassEndpointMarkedResidualThreshold
          hasGhost hasOrigin hasEndpoint ≤ R.card :=
      (Finset.mem_filter.mp hRfilter).2
    have hRcardLe :
        R.card ≤
          (finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card :=
      Finset.card_le_card (Finset.mem_powerset.mp hRpow)
    refine Finset.mem_biUnion.mpr ⟨R.card, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨by simpa using Nat.lt_succ_of_le hRcardLe, hRthreshold⟩
    · exact Finset.mem_image.mpr
        ⟨R, Finset.mem_filter.mpr ⟨hRpow, rfl⟩, hSR⟩
  have hpair :
      ((K : Finset ℕ) : Set ℕ).PairwiseDisjoint
        (fun k =>
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
            v hasGhost hasOrigin hasEndpoint k) := by
    simpa [K] using
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage_pairwiseDisjoint
        v hasGhost hasOrigin hasEndpoint
  calc
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint
        ≤
          ∑ S ∈ K.biUnion
              (fun k =>
                finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
                  v hasGhost hasOrigin hasEndpoint k),
            finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
              β H n Ω v S := by
          unfold finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun S _hSbig _hSnot =>
              finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
                hβ hH n Ω v S)
    _ =
          ∑ k ∈ K,
            ∑ S ∈
              finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImage
                v hasGhost hasOrigin hasEndpoint k,
              finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                β H n Ω v S := by
      exact Finset.sum_biUnion hpair
    _ =
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum
          β H n Ω v hasGhost hasOrigin hasEndpoint := by
      simp [
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum,
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum,
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex,
        K]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum_eq_thresholdImageSourceClassSum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    (hasGhost hasOrigin hasEndpoint : Bool) :
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint =
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
        β H n Ω v hasGhost hasOrigin hasEndpoint := by
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum
  rw [
    finiteBoundaryGhostSourceClassEndpointUnmarkedOptions_powerset_filter_markedResidualCard_eq_threshold
      hv hasGhost hasOrigin hasEndpoint]

end Exact3D
end StatMech
