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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part112
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapComponentStrictCanonicalRatioShareSum_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical) :
    BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [
    h β hβpos hβc,
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry
      β hβpos hβc] with n hn hnpos
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  have hDpos : 0 < D := by
    simpa [D] using hnpos H hH v hv
  have hBnonneg :
      SourceClassEndpointMembershipLiveBudget15.Nonneg
        (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
          β H n Ωnz v) :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15_nonneg
      (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have hshellNonneg :
      0 ≤ residualThresholdShellBudget15CanonicalShellBudgetShare
        β H n Ωnz v := by
    exact
      div_nonneg
        (SourceClassEndpointMembershipLiveBudget15.total_nonneg hBnonneg)
        (le_of_lt hDpos)
  have hfour :
      residualThresholdShellBudget15CanonicalOnePointShare β H n Ωnz v +
          residualThresholdShellBudget15CanonicalBoundaryPairShare
            β H n Ωnz v +
          residualThresholdShellBudget15CanonicalEmptyBoundaryShare
            β H n Ωnz v +
          residualThresholdShellBudget15CanonicalShellBudgetShare
            β H n Ωnz v < 1 := by
    simpa [Ωnz] using hn H hH Ω v hv
  linarith

set_option linter.style.longLine false in


theorem boundaryCrossingCapComponentStrictShareScheduleBudget_of_canonicalRatioShareSum
    (h :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical) :
    BoundaryCrossingCapComponentStrictShareScheduleBudgetPositiveSubcritical
      residualThresholdShellBudget15CanonicalOnePointShare
      residualThresholdShellBudget15CanonicalBoundaryPairShare
      residualThresholdShellBudget15CanonicalEmptyBoundaryShare := by
  intro β hβpos hβc
  filter_upwards [
    h β hβpos hβc,
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry
      β hβpos hβc] with n hnsum hnpos
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg hcap honeFactor) (le_of_lt hDpos)
  · exact div_nonneg (mul_nonneg hcap hboundaryFactor) (le_of_lt hDpos)
  · exact div_nonneg hempty (le_of_lt hDpos)
  · simpa [Ωnz] using hnsum H hH Ω v hv

set_option linter.style.longLine false in


theorem boundaryCrossingCapComponentStrictShareScheduleAbsorption_of_canonicalRatioShareSum
    (h :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical) :
    BoundaryCrossingCapComponentStrictShareScheduleAbsorptionPositiveSubcritical
      residualThresholdShellBudget15CanonicalOnePointShare
      residualThresholdShellBudget15CanonicalBoundaryPairShare
      residualThresholdShellBudget15CanonicalEmptyBoundaryShare :=
  boundaryCrossingCapComponentStrictShareScheduleAbsorption_of_components
    (boundaryCrossingCapComponentStrictShareScheduleBudget_of_canonicalRatioShareSum
      h)
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePoint_of_canonicalRatioShare
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPair_of_canonicalRatioShare
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundary_of_canonicalRatioShare

set_option linter.style.longLine false in


theorem boundaryCrossingCapComponentStrictShareAbsorption_of_canonicalRatioShareSum
    (h :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical) :
    BoundaryCrossingCapComponentStrictSharePositiveSubcritical :=
  boundaryCrossingCapComponentStrictShareAbsorption_of_shareSchedule
    (boundaryCrossingCapComponentStrictShareScheduleAbsorption_of_canonicalRatioShareSum
      h)

set_option linter.style.longLine false in


theorem boundaryCrossingCapComponentStrictCanonicalRatioShareSum_of_componentStrictSum
    (hstrict :
      BoundaryCrossingCapComponentStrictSumPositiveSubcritical) :
    BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [
    hstrict β hβpos hβc,
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry
      β hβpos hβc] with n hnstrict hnDpos
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let one :=
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
      β H n
  let boundary :=
    cap *
      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
        β H n v
  let empty := finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
    β H n v
  have hDpos : 0 < D := by
    simpa [D] using hnDpos H hH v hv
  have hpaid : one + boundary + empty < D := by
    simpa [one, boundary, empty, Ωnz, cap, D] using
      hnstrict H hH Ω v hv
  have hratio :
      one / D + boundary / D + empty / D < 1 :=
    (three_ratio_sum_lt_one_iff_sum_lt_of_pos hDpos).2 hpaid
  simpa [
    residualThresholdShellBudget15CanonicalOnePointShare,
    residualThresholdShellBudget15CanonicalBoundaryPairShare,
    residualThresholdShellBudget15CanonicalEmptyBoundaryShare,
    one, boundary, empty, Ωnz, cap, D] using hratio

set_option linter.style.longLine false in


theorem boundaryCrossingCapComponentStrictSumAbsorption_of_componentStrictShare
    (hshare : BoundaryCrossingCapComponentStrictSharePositiveSubcritical) :
    BoundaryCrossingCapComponentStrictSumPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [
    hshare β hβpos hβc,
    finiteQ2BoundaryVertexDenominatorPositive_from_boxGeometry
      β hβpos hβc] with n hnshare hnDpos
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hnshare H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare,
      _honeShareNonneg, _hboundaryPairShareNonneg, _hemptyBoundaryShareNonneg,
      hshareSum, hone, hboundary, hempty⟩
  have hDpos : 0 < D := by
    simpa [D] using hnDpos H hH v hv
  have hpaidLe :
      cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v ≤
        (oneShare + boundaryPairShare + emptyBoundaryShare) * D := by
    calc
      cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v
          ≤ oneShare * D + boundaryPairShare * D + emptyBoundaryShare * D := by
        exact add_le_add (add_le_add hone hboundary) hempty
      _ = (oneShare + boundaryPairShare + emptyBoundaryShare) * D := by
        ring
  have hshareScale :
      (oneShare + boundaryPairShare + emptyBoundaryShare) * D < D := by
    calc
      (oneShare + boundaryPairShare + emptyBoundaryShare) * D < 1 * D :=
        mul_lt_mul_of_pos_right hshareSum hDpos
      _ = D := by ring
  exact hpaidLe.trans_lt hshareScale

set_option linter.style.longLine false in


theorem boundaryCrossingCapComponentStrictSumAbsorption_of_componentStrictCanonicalRatioShareSum
    (h :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical) :
    BoundaryCrossingCapComponentStrictSumPositiveSubcritical :=
  boundaryCrossingCapComponentStrictSumAbsorption_of_componentStrictShare
    (boundaryCrossingCapComponentStrictShareAbsorption_of_canonicalRatioShareSum
      h)

set_option linter.style.longLine false in


theorem boundaryCrossingCapComponentStrictCanonicalRatioShareSum_iff_componentStrictSum :
    BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical ↔
      BoundaryCrossingCapComponentStrictSumPositiveSubcritical :=
  ⟨boundaryCrossingCapComponentStrictSumAbsorption_of_componentStrictCanonicalRatioShareSum,
    boundaryCrossingCapComponentStrictCanonicalRatioShareSum_of_componentStrictSum⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictSum
    (h :
      BoundaryCrossingCapComponentStrictSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
        β H n v
  have hpaid : paid < D := by
    simpa [paid, Ωnz, cap, D] using hn H hH Ω v hv
  have hRpos : 0 < D - paid := sub_pos.mpr hpaid
  simpa [paid, Ωnz, cap, D] using hRpos

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictShare
    (h :
      BoundaryCrossingCapComponentStrictSharePositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictSum
    (boundaryCrossingCapComponentStrictSumAbsorption_of_componentStrictShare
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
    (h :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictShare
    (boundaryCrossingCapComponentStrictShareAbsorption_of_canonicalRatioShareSum
      h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderNonnegative_of_boundaryCrossingRemainderPositive
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderNonnegativePositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  exact le_of_lt (by simpa [Ωnz, cap, D] using hn H hH Ω v hv)

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
    {schedule : LiveSingletonOptionShareSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
      schedule := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  simpa [Ωnz, cap, D, paid, R] using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderNonnegative_of_boundaryCrossingCapComponentSum
    (h :
      BoundaryCrossingCapComponentSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderNonnegativePositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  have hthree :
      cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                β H n +
            cap *
              finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                β H n v +
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
              β H n v ≤
        D := by
    simpa [Ωnz, cap, D] using hn H hH Ω v hv
  linarith

end Exact3D
end StatMech
