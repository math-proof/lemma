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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part68
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum_of_strictCanonicalRatioShareSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  exact le_of_lt (hn H hH Ω v hv)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBudget_of_canonicalRatioShareSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBudgetPositiveSubcritical
      residualThresholdShellBudget15CanonicalOnePointShare
      residualThresholdShellBudget15CanonicalBoundaryPairShare
      residualThresholdShellBudget15CanonicalEmptyBoundaryShare
      residualThresholdShellBudget15CanonicalShellBudgetShare := by
  intro β hβpos hβc
  filter_upwards [
    h β hβpos hβc,
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry β hβpos hβc] with
    n hnsum hnpos
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  have hDpos : 0 < D := by
    simpa [D] using hnpos H hH v hv
  have hcap : 0 ≤ boundaryCrossingCap n Ωnz := by
    simpa [boundaryCrossingCap] using
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_nonneg
        Ωnz
  have honeFactor :
      0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
        β H n :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_nonneg
      (le_of_lt hβpos) (le_of_lt hH)
  have hboundaryFactor :
      0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
        β H n v :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_nonneg
      (le_of_lt hβpos) (le_of_lt hH) v
  have hempty :
      0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
        β H n v :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm_nonneg
      (le_of_lt hβpos) (le_of_lt hH) v
  have hBnonneg :
      SourceClassEndpointMembershipLiveBudget15.Nonneg
        (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
          β H n Ωnz v) :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15_nonneg
      (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg hcap honeFactor) (le_of_lt hDpos)
  · exact div_nonneg (mul_nonneg hcap hboundaryFactor) (le_of_lt hDpos)
  · exact div_nonneg hempty (le_of_lt hDpos)
  · exact
      div_nonneg
        (SourceClassEndpointMembershipLiveBudget15.total_nonneg hBnonneg)
        (le_of_lt hDpos)
  · simpa [Ωnz] using hnsum H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePoint_of_canonicalRatioShare :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePointPositiveSubcritical
      residualThresholdShellBudget15CanonicalOnePointShare := by
  intro β hβpos hβc
  filter_upwards [
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry β hβpos hβc] with
    n hnpos
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  have hDpos : 0 < D := by
    simpa [D] using hnpos H hH v hv
  dsimp [residualThresholdShellBudget15CanonicalOnePointShare, D]
  rw [div_mul_cancel₀ _ hDpos.ne']

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPair_of_canonicalRatioShare :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPairPositiveSubcritical
      residualThresholdShellBudget15CanonicalBoundaryPairShare := by
  intro β hβpos hβc
  filter_upwards [
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry β hβpos hβc] with
    n hnpos
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  have hDpos : 0 < D := by
    simpa [D] using hnpos H hH v hv
  dsimp [residualThresholdShellBudget15CanonicalBoundaryPairShare, D]
  rw [div_mul_cancel₀ _ hDpos.ne']

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundary_of_canonicalRatioShare :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundaryPositiveSubcritical
      residualThresholdShellBudget15CanonicalEmptyBoundaryShare := by
  intro β hβpos hβc
  filter_upwards [
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry β hβpos hβc] with
    n hnpos
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  have hDpos : 0 < D := by
    simpa [D] using hnpos H hH v hv
  dsimp [residualThresholdShellBudget15CanonicalEmptyBoundaryShare, D]
  rw [div_mul_cancel₀ _ hDpos.ne']

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudget_of_canonicalRatioShare :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudgetPositiveSubcritical
      residualThresholdShellBudget15CanonicalShellBudgetShare := by
  intro β hβpos hβc
  filter_upwards [
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry β hβpos hβc] with
    n hnpos
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  have hDpos : 0 < D := by
    simpa [D] using hnpos H hH v hv
  dsimp [residualThresholdShellBudget15CanonicalShellBudgetShare, D]
  rw [div_mul_cancel₀ _ hDpos.ne']

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorption_of_canonicalRatioShareSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorptionPositiveSubcritical
      residualThresholdShellBudget15CanonicalOnePointShare
      residualThresholdShellBudget15CanonicalBoundaryPairShare
      residualThresholdShellBudget15CanonicalEmptyBoundaryShare
      residualThresholdShellBudget15CanonicalShellBudgetShare :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorption_of_components
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBudget_of_canonicalRatioShareSum
      h)
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePoint_of_canonicalRatioShare
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPair_of_canonicalRatioShare
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundary_of_canonicalRatioShare
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudget_of_canonicalRatioShare

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorption_of_shareSchedule
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorptionPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  exact
    ⟨oneShare β H n Ωnz v,
      boundaryPairShare β H n Ωnz v,
      emptyBoundaryShare β H n Ωnz v,
      shellBudgetShare β H n Ωnz v,
      hn H hH Ω v hv⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareAbsorption_of_strictShareSchedule
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleAbsorptionPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  exact
    ⟨oneShare β H n Ωnz v,
      boundaryPairShare β H n Ωnz v,
      emptyBoundaryShare β H n Ωnz v,
      shellBudgetShare β H n Ωnz v,
      hn H hH Ω v hv⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareAbsorption_of_components
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hbudget :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleBudgetPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hone :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePointPositiveSubcritical
        oneShare)
    (hboundary :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPairPositiveSubcritical
        boundaryPairShare)
    (hempty :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundaryPositiveSubcritical
        emptyBoundaryShare)
    (hshell :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudgetPositiveSubcritical
        shellBudgetShare) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareAbsorption_of_strictShareSchedule
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleAbsorption_of_components
      hbudget hone hboundary hempty hshell)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorption_of_residualThresholdShellBudget15ComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, sectorShare,
      honeShare, hboundaryShare, hemptyShare, hsectorNonneg, hshareSum,
      hone, hboundary, hempty, hfieldwise⟩
  refine
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, sectorShare.total,
      honeShare, hboundaryShare, hemptyShare, ?_, hshareSum, hone,
      hboundary, hempty, ?_⟩
  · exact SourceClassEndpointMembershipLiveBudget15.total_nonneg
      hsectorNonneg
  · exact SourceClassEndpointMembershipLiveBudget15.total_le_mul_of_fieldwiseLeMul
      hfieldwise

end Exact3D
end StatMech
