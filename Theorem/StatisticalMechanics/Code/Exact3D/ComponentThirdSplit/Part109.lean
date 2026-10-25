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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part115
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareScheduleAbsorption_of_boundaryCrossingRemainderPositive_boundaryCrossingRemainder
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (habs :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareScheduleAbsorptionPositiveSubcritical
      residualThresholdShellBudget15BoundaryCrossingRemainderCanonicalShareSchedule := by
  intro β hβpos hβc
  filter_upwards [hpos β hβpos hβc, habs β hβpos hβc] with
    n hnpos hnabs
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  let R :=
    D -
      (cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
            β H n +
        cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
          β H n v)
  have hRpos : 0 < R := by
    simpa [R, Ωnz, cap, D] using hnpos H hH Ω v hv
  have hBnonneg :
      SourceClassEndpointMembershipLiveBudget15.Nonneg B := by
    simpa [B] using
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have hBtotal : B.total ≤ R := by
    simpa [R, B, Ωnz, cap, D] using hnabs H hH Ω v hv
  have hnonneg :
      SourceClassEndpointMembershipLiveBudget15.Nonneg
        (SourceClassEndpointMembershipLiveBudget15.normalized B R) :=
    SourceClassEndpointMembershipLiveBudget15.normalized_nonneg
      hBnonneg (le_of_lt hRpos)
  have htotal :
      (SourceClassEndpointMembershipLiveBudget15.normalized B R).total ≤ 1 :=
    SourceClassEndpointMembershipLiveBudget15.normalized_total_le_one_of_total_le
      hRpos hBtotal
  have hfield :
      SourceClassEndpointMembershipLiveBudget15.FieldwiseLeMul
        B (SourceClassEndpointMembershipLiveBudget15.normalized B R) R :=
    SourceClassEndpointMembershipLiveBudget15.fieldwiseLeMul_normalized_of_pos
      B hRpos
  simpa [
    residualThresholdShellBudget15BoundaryCrossingRemainderCanonicalShareSchedule,
    Ωnz, cap, D, B, R] using
    ⟨hnonneg, htotal, hfield⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareScheduleAbsorption_of_boundaryCrossingRemainderStrict
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareScheduleAbsorptionPositiveSubcritical
      residualThresholdShellBudget15BoundaryCrossingRemainderCanonicalShareSchedule := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  let R :=
    D -
      (cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
            β H n +
        cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
          β H n v)
  have hBstrict : B.total < R := by
    simpa [R, B, Ωnz, cap, D] using hn H hH Ω v hv
  have hBnonneg :
      SourceClassEndpointMembershipLiveBudget15.Nonneg B := by
    simpa [B] using
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have hBtotalNonneg : 0 ≤ B.total :=
    SourceClassEndpointMembershipLiveBudget15.total_nonneg hBnonneg
  have hRpos : 0 < R := lt_of_le_of_lt hBtotalNonneg hBstrict
  have hnonneg :
      SourceClassEndpointMembershipLiveBudget15.Nonneg
        (SourceClassEndpointMembershipLiveBudget15.normalized B R) :=
    SourceClassEndpointMembershipLiveBudget15.normalized_nonneg
      hBnonneg (le_of_lt hRpos)
  have htotal :
      (SourceClassEndpointMembershipLiveBudget15.normalized B R).total < 1 :=
    SourceClassEndpointMembershipLiveBudget15.normalized_total_lt_one_of_total_lt
      hRpos hBstrict
  have hfield :
      SourceClassEndpointMembershipLiveBudget15.FieldwiseLeMul
        B (SourceClassEndpointMembershipLiveBudget15.normalized B R) R :=
    SourceClassEndpointMembershipLiveBudget15.fieldwiseLeMul_normalized_of_pos
      B hRpos
  simpa [
    residualThresholdShellBudget15BoundaryCrossingRemainderCanonicalShareSchedule,
    Ωnz, cap, D, B, R] using
    ⟨hnonneg, htotal, hfield⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorption_of_shareSchedule
    {sectorShare :
      ResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareScheduleAbsorptionPositiveSubcritical
        sectorShare) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  exact ⟨sectorShare β H n Ωnz v, hn H hH Ω v hv⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_strictShareSchedule
    {sectorShare :
      ResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareScheduleAbsorptionPositiveSubcritical
        sectorShare) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  exact ⟨sectorShare β H n Ωnz v, hn H hH Ω v hv⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareScheduleAbsorption_of_strictShareSchedule
    {sectorShare :
      ResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareScheduleAbsorptionPositiveSubcritical
        sectorShare) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareScheduleAbsorptionPositiveSubcritical
      sectorShare := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with ⟨hnonneg, htotal, hfield⟩
  exact ⟨hnonneg, le_of_lt htotal, hfield⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorption_of_boundaryCrossingRemainderStrictShare
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨sectorShare, hnonneg, htotal, hfield⟩
  exact ⟨sectorShare, hnonneg, le_of_lt htotal, hfield⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorption_of_boundaryCrossingRemainderPositive_strictRemainderShare
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hpos β hβpos hβc, hshare β hβpos hβc] with
    n hnpos hnshare
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  let R :=
    D -
      (cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
            β H n +
        cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
          β H n v)
  have hRpos : 0 < R := by
    simpa [R, Ωnz, cap, D] using hnpos H hH Ω v hv
  rcases hnshare H hH Ω v hv with
    ⟨sectorShare, _hsectorNonneg, hshareTotal, hfield⟩
  have hBbound :
      B.total ≤ sectorShare.total * R :=
    SourceClassEndpointMembershipLiveBudget15.total_le_mul_of_fieldwiseLeMul
      hfield
  have hscale : sectorShare.total * R < R := by
    calc
      sectorShare.total * R < 1 * R :=
        mul_lt_mul_of_pos_right hshareTotal hRpos
      _ = R := by ring
  have hstrict : B.total < R := hBbound.trans_lt hscale
  simpa [R, B, Ωnz, cap, D] using hstrict

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorption_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum_strictRemainderShareSchedule
    {sectorShare :
      ResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule}
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareScheduleAbsorptionPositiveSubcritical
        sectorShare) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorption_of_boundaryCrossingRemainderPositive_strictRemainderShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hstrict)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_strictShareSchedule
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorption_of_boundaryCrossingRemainderPositive_strictRemainderShare
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorption_of_boundaryCrossingRemainderStrict
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorption_of_boundaryCrossingRemainderPositive_strictRemainderShare
      hpos hshare)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_of_boundaryCrossingRemainderPositive_strictRemainderShare
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_of_strictComponentDenominatorFreeSum
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorption_of_boundaryCrossingRemainderPositive_strictRemainderShare
      hpos hshare)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum_strictRemainderShare
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_of_boundaryCrossingRemainderPositive_strictRemainderShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hstrict)
    hshare

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum_strictRemainderShareSchedule
    {sectorShare :
      ResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule}
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareScheduleAbsorptionPositiveSubcritical
        sectorShare) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum_strictRemainderShare
    hstrict
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareAbsorption_of_strictShareSchedule
      hshare)

end Exact3D
end StatMech
