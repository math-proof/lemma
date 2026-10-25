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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part110
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption_of_strictComponentDenominatorFreeSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  exact le_of_lt (hn H hH Ω v hv)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_of_strictComponentDenominatorFreeSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [
    h β hβpos hβc,
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry
      β hβpos hβc] with n hn hnpos
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  have hDpos : 0 < D := by
    simpa [D] using hnpos H hH v hv
  have hscalar :
      cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v +
          B.total < D := by
    simpa [Ωnz, cap, D, B] using hn H hH Ω v hv
  have hratio :
      (cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n) / D +
          (cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v) / D +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v / D +
          B.total / D < 1 :=
    (four_ratio_sum_lt_one_iff_sum_lt_of_pos hDpos).2 hscalar
  simpa [
    residualThresholdShellBudget15CanonicalOnePointShare,
    residualThresholdShellBudget15CanonicalBoundaryPairShare,
    residualThresholdShellBudget15CanonicalEmptyBoundaryShare,
    residualThresholdShellBudget15CanonicalShellBudgetShare,
    Ωnz, cap, D, B] using hratio

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorption_of_strictCanonicalRatioShareSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [
    h β hβpos hβc,
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry
      β hβpos hβc] with n hn hnpos
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  have hDpos : 0 < D := by
    simpa [D] using hnpos H hH v hv
  have hcanonical :
      residualThresholdShellBudget15CanonicalOnePointShare β H n Ωnz v +
          residualThresholdShellBudget15CanonicalBoundaryPairShare
            β H n Ωnz v +
          residualThresholdShellBudget15CanonicalEmptyBoundaryShare
            β H n Ωnz v +
          residualThresholdShellBudget15CanonicalShellBudgetShare
            β H n Ωnz v < 1 := by
    simpa [Ωnz] using hn H hH Ω v hv
  have hratio :
      (cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n) / D +
          (cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v) / D +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v / D +
          B.total / D < 1 := by
    simpa [
      residualThresholdShellBudget15CanonicalOnePointShare,
      residualThresholdShellBudget15CanonicalBoundaryPairShare,
      residualThresholdShellBudget15CanonicalEmptyBoundaryShare,
      residualThresholdShellBudget15CanonicalShellBudgetShare,
      cap, D, B] using hcanonical
  have hscalar :
      cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v +
          B.total < D :=
    (four_ratio_sum_lt_one_iff_sum_lt_of_pos hDpos).1 hratio
  simpa [Ωnz, cap, D, B] using hscalar

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_iff_strictComponentDenominatorFreeSum :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical :=
  ⟨boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorption_of_strictCanonicalRatioShareSum,
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_of_strictComponentDenominatorFreeSum⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorption_of_strictAggregateComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [
    h β hβpos hβc,
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry
      β hβpos hβc] with n hn hnpos
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare, shellBudgetShare,
      _honeShareNonneg, _hboundaryShareNonneg, _hemptyShareNonneg,
      _hshellShareNonneg, hshareSum, hone, hboundary, hempty, hshell⟩
  have hDpos : 0 < D := by
    simpa [D] using hnpos H hH v hv
  have hle :
      cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v +
            B.total ≤
        (oneShare + boundaryPairShare + emptyBoundaryShare +
            shellBudgetShare) * D := by
    calc
      cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v +
            B.total
          ≤
        oneShare * D + boundaryPairShare * D + emptyBoundaryShare * D +
            shellBudgetShare * D := by
          linarith
      _ =
        (oneShare + boundaryPairShare + emptyBoundaryShare +
            shellBudgetShare) * D := by
          ring
  have hlt :
      (oneShare + boundaryPairShare + emptyBoundaryShare +
          shellBudgetShare) * D < D := by
    have hmul :
        (oneShare + boundaryPairShare + emptyBoundaryShare +
            shellBudgetShare) * D < 1 * D :=
      mul_lt_mul_of_pos_right hshareSum hDpos
    simpa using hmul
  have hstrict :
      cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v +
            B.total < D :=
    lt_of_le_of_lt hle hlt
  simpa [Ωnz, cap, D, B] using hstrict

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_of_strictAggregateComponentShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_of_strictComponentDenominatorFreeSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorption_of_strictAggregateComponentShare
      h)

end Exact3D
end StatMech
