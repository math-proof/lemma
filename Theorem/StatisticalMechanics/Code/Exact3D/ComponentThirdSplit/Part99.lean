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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part104
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
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
  let classifiedCount : ℝ :=
    ∑ S ∈
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v 1,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true S).card : ℝ)
  rcases hn H hH Ω v hv with
    ⟨remainingShare, singletonMaxCapShare, tailShare, hRpos,
      _hremainingShareNonneg, _hsingletonShareNonneg, _htailShareNonneg,
      hremaining, hcapBound, htailBound, hshareStrict⟩
  refine
    ⟨remainingShare * R, singletonMaxCapShare * R, tailShare * R,
      hremaining, hcapBound, htailBound, ?_⟩
  have hscaled :
      (remainingShare + (classifiedCount * singletonMaxCapShare + tailShare)) *
          R <
        1 * R :=
    mul_lt_mul_of_pos_right hshareStrict hRpos
  have hrewrite :
      remainingShare * R +
          (classifiedCount * (singletonMaxCapShare * R) + tailShare * R) =
        (remainingShare + (classifiedCount * singletonMaxCapShare + tailShare)) *
          R := by
    ring
  calc
    remainingShare * R +
        (classifiedCount * (singletonMaxCapShare * R) + tailShare * R)
        =
          (remainingShare + (classifiedCount * singletonMaxCapShare + tailShare)) *
            R :=
          hrewrite
    _ < 1 * R := hscaled
    _ = D - paid := by
      simp [R]

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
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
  let classifiedCount : ℝ :=
    ∑ S ∈
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v 1,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true S).card : ℝ)
  let remaining :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
      β H n Ωnz v
  let singletonMaxCap :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
      β H n Ωnz v hv
  let tail :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
      β H n Ωnz v
  have hscalar : remaining + (classifiedCount * singletonMaxCap + tail) < R := by
    simpa [remaining, singletonMaxCap, tail, classifiedCount, R, Ωnz, cap, D, paid]
      using hn H hH Ω v hv
  have hremainingNonneg : 0 ≤ remaining := by
    simpa [remaining] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have hsingletonNonneg : 0 ≤ singletonMaxCap := by
    simpa [singletonMaxCap] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz hv
  have htailNonneg : 0 ≤ tail := by
    simpa [tail] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have hcountNonneg : 0 ≤ classifiedCount := by
    dsimp [classifiedCount]
    exact Finset.sum_nonneg fun S _hS => Nat.cast_nonneg _
  have hlhsNonneg : 0 ≤ remaining + (classifiedCount * singletonMaxCap + tail) := by
    exact
      add_nonneg hremainingNonneg
        (add_nonneg (mul_nonneg hcountNonneg hsingletonNonneg) htailNonneg)
  have hRpos : 0 < R := lt_of_le_of_lt hlhsNonneg hscalar
  refine
    ⟨remaining / R, singletonMaxCap / R, tail / R,
      hRpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg hremainingNonneg (le_of_lt hRpos)
  · exact div_nonneg hsingletonNonneg (le_of_lt hRpos)
  · exact div_nonneg htailNonneg (le_of_lt hRpos)
  · change remaining ≤ (remaining / R) * R
    exact le_of_eq (by field_simp [hRpos.ne'])
  · change singletonMaxCap ≤ (singletonMaxCap / R) * R
    exact le_of_eq (by field_simp [hRpos.ne'])
  · change tail ≤ (tail / R) * R
    exact le_of_eq (by field_simp [hRpos.ne'])
  · change remaining / R + (classifiedCount * (singletonMaxCap / R) + tail / R) < 1
    have hscalar' : remaining + classifiedCount * singletonMaxCap + tail < R := by
      simpa [add_assoc] using hscalar
    have hratio :
        remaining / R + (classifiedCount * singletonMaxCap) / R + tail / R < 1 :=
      (three_ratio_sum_lt_one_iff_sum_lt_of_pos
        (one := remaining)
        (boundary := classifiedCount * singletonMaxCap)
        (empty := tail)
        hRpos).2 hscalar'
    have hrewrite :
        remaining / R + (classifiedCount * (singletonMaxCap / R) + tail / R) =
          remaining / R + (classifiedCount * singletonMaxCap) / R + tail / R := by
      ring
    simpa [hrewrite] using hratio

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_iff_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFree :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical :=
  ⟨fun h =>
      boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
        (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
          h),
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFree⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
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
  let classifiedCount : ℝ :=
    ∑ S ∈
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v 1,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true S).card : ℝ)
  let singletonOptionClassifiedCount : ℝ :=
    ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))).card : ℝ)
  have hcountEq : classifiedCount = singletonOptionClassifiedCount := by
    dsimp [classifiedCount, singletonOptionClassifiedCount]
    exact
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_one_sum_eq_unmarkedOptions_singleton_sum
        v
        (fun S =>
          ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ωnz true true true S).card : ℝ))
  rcases hn H hH Ω v hv with
    ⟨remainingBound, singletonMaxCapBound, tailBound,
      hremaining, hcapBound, htailBound, hstrict⟩
  refine
    ⟨remainingBound, singletonMaxCapBound, tailBound,
      hremaining, hcapBound, htailBound, ?_⟩
  simpa [Ωnz, cap, D, paid, classifiedCount, singletonOptionClassifiedCount,
    hcountEq] using hstrict

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
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
  let classifiedCount : ℝ :=
    ∑ S ∈
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v 1,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true S).card : ℝ)
  let singletonOptionClassifiedCount : ℝ :=
    ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))).card : ℝ)
  have hcountEq : classifiedCount = singletonOptionClassifiedCount := by
    dsimp [classifiedCount, singletonOptionClassifiedCount]
    exact
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_one_sum_eq_unmarkedOptions_singleton_sum
        v
        (fun S =>
          ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ωnz true true true S).card : ℝ))
  rcases hn H hH Ω v hv with
    ⟨remainingBound, singletonMaxCapBound, tailBound,
      hremaining, hcapBound, htailBound, hstrict⟩
  refine
    ⟨remainingBound, singletonMaxCapBound, tailBound,
      hremaining, hcapBound, htailBound, ?_⟩
  simpa [Ωnz, cap, D, paid, classifiedCount, singletonOptionClassifiedCount,
    hcountEq] using hstrict

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_iff_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFree :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical :=
  ⟨boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree,
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFree⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
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
  let classifiedCount : ℝ :=
    ∑ S ∈
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v 1,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true S).card : ℝ)
  let singletonOptionClassifiedCount : ℝ :=
    ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))).card : ℝ)
  have hcountEq : classifiedCount = singletonOptionClassifiedCount := by
    dsimp [classifiedCount, singletonOptionClassifiedCount]
    exact
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_one_sum_eq_unmarkedOptions_singleton_sum
        v
        (fun S =>
          ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ωnz true true true S).card : ℝ))
  rcases hn H hH Ω v hv with
    ⟨remainingShare, singletonMaxCapShare, tailShare, hRpos,
      hremainingShareNonneg, hsingletonShareNonneg, htailShareNonneg,
      hremaining, hcapBound, htailBound, hshareStrict⟩
  refine
    ⟨remainingShare, singletonMaxCapShare, tailShare,
      hRpos, hremainingShareNonneg, hsingletonShareNonneg,
      htailShareNonneg, hremaining, hcapBound, htailBound, ?_⟩
  simpa [Ωnz, cap, D, paid, R, classifiedCount,
    singletonOptionClassifiedCount, hcountEq] using hshareStrict

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
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
  let classifiedCount : ℝ :=
    ∑ S ∈
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v 1,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true S).card : ℝ)
  let singletonOptionClassifiedCount : ℝ :=
    ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))).card : ℝ)
  have hcountEq : classifiedCount = singletonOptionClassifiedCount := by
    dsimp [classifiedCount, singletonOptionClassifiedCount]
    exact
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_one_sum_eq_unmarkedOptions_singleton_sum
        v
        (fun S =>
          ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ωnz true true true S).card : ℝ))
  rcases hn H hH Ω v hv with
    ⟨remainingShare, singletonMaxCapShare, tailShare, hRpos,
      hremainingShareNonneg, hsingletonShareNonneg, htailShareNonneg,
      hremaining, hcapBound, htailBound, hshareStrict⟩
  refine
    ⟨remainingShare, singletonMaxCapShare, tailShare,
      hRpos, hremainingShareNonneg, hsingletonShareNonneg,
      htailShareNonneg, hremaining, hcapBound, htailBound, ?_⟩
  simpa [Ωnz, cap, D, paid, R, classifiedCount,
    singletonOptionClassifiedCount, hcountEq] using hshareStrict

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_iff_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFree :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical :=
  ⟨boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree,
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareResidualCaseClassifiedCountTailStrictRemainderDenominatorFree⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
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
  let supportCount : ℝ :=
    ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ωnz v true true true 1).card : ℝ)
  have hcardOne :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
          β H n Ωnz v ≤
        supportCount *
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
            β H n Ωnz v hv := by
    simpa [supportCount] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_le_supportResidualExactCardSourceClassSet_card_mul_singletonMaxCap_of_boundary
        (β := β) (H := H) (n := n) (Ω := Ωnz) (v := v) hv
  have htail :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
          β H n Ωnz v +
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
          β H n Ωnz v ≤
        supportCount *
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
              β H n Ωnz v hv +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v :=
    add_le_add hcardOne le_rfl
  have hmono :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
          β H n Ωnz v +
        (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
            β H n Ωnz v +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v) ≤
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
            β H n Ωnz v +
          (supportCount *
              finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
                β H n Ωnz v hv +
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
              β H n Ωnz v) :=
    add_le_add le_rfl htail
  exact
    lt_of_le_of_lt hmono
      (by
        simpa [Ωnz, cap, D, paid, supportCount] using hn H hH Ω v hv)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapBoxVolumeTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapBoxVolumeTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
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
  let supportCount : ℝ :=
    ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ωnz v true true true 1).card : ℝ)
  let fullCount : ℝ := (((2 * n + 1) ^ 3 - 2 : ℕ) : ℝ)
  let singletonMaxCap :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
      β H n Ωnz v hv
  have hcountNat :
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
          n Ωnz v true true true 1).card ≤
        ((2 * n + 1) ^ 3 - 2) :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_le_box_volume_sub_two_of_boundary
      Ωnz hv true true true
  have hcountLe : supportCount ≤ fullCount := by
    dsimp [supportCount, fullCount]
    exact_mod_cast hcountNat
  have hcapNonneg : 0 ≤ singletonMaxCap := by
    simpa [singletonMaxCap] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz hv
  have hmul : supportCount * singletonMaxCap ≤ fullCount * singletonMaxCap :=
    mul_le_mul_of_nonneg_right hcountLe hcapNonneg
  have htail :
      supportCount * singletonMaxCap +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v ≤
        fullCount * singletonMaxCap +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v :=
    add_le_add hmul le_rfl
  have hmono :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
          β H n Ωnz v +
        (supportCount * singletonMaxCap +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v) ≤
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
            β H n Ωnz v +
          (fullCount * singletonMaxCap +
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
              β H n Ωnz v) :=
    add_le_add le_rfl htail
  exact
    lt_of_le_of_lt hmono
      (by
        simpa [Ωnz, cap, D, paid, supportCount, fullCount, singletonMaxCap]
          using hn H hH Ω v hv)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
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
  let supportCount : ℝ :=
    ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ωnz v true true true 1).card : ℝ)
  rcases hn H hH Ω v hv with
    ⟨remainingBound, singletonMaxCapBound, tailBound,
      hremaining, hcapBound, htailBound, hstrict⟩
  have hcountNonneg : 0 ≤ supportCount := by
    exact Nat.cast_nonneg _
  have hcapMul :
      supportCount *
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
            β H n Ωnz v hv ≤
        supportCount * singletonMaxCapBound :=
    mul_le_mul_of_nonneg_left hcapBound hcountNonneg
  have htail :
      supportCount *
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
            β H n Ωnz v hv +
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
          β H n Ωnz v ≤
        supportCount * singletonMaxCapBound + tailBound :=
    add_le_add hcapMul htailBound
  have hmono :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
          β H n Ωnz v +
        (supportCount *
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
              β H n Ωnz v hv +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v) ≤
        remainingBound + (supportCount * singletonMaxCapBound + tailBound) :=
    add_le_add hremaining htail
  exact
    lt_of_le_of_lt hmono
      (by
        simpa [Ωnz, cap, D, paid, supportCount] using hstrict)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
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
  let supportCount : ℝ :=
    ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ωnz v true true true 1).card : ℝ)
  rcases hn H hH Ω v hv with
    ⟨remainingShare, singletonMaxCapShare, tailShare, hRpos,
      _hremainingShareNonneg, _hsingletonShareNonneg, _htailShareNonneg,
      hremaining, hcapBound, htailBound, hshareStrict⟩
  refine
    ⟨remainingShare * R, singletonMaxCapShare * R, tailShare * R,
      hremaining, hcapBound, htailBound, ?_⟩
  have hscaled :
      (remainingShare + (supportCount * singletonMaxCapShare + tailShare)) *
          R <
        1 * R :=
    mul_lt_mul_of_pos_right hshareStrict hRpos
  have hrewrite :
      remainingShare * R +
          (supportCount * (singletonMaxCapShare * R) + tailShare * R) =
        (remainingShare + (supportCount * singletonMaxCapShare + tailShare)) *
          R := by
    ring
  calc
    remainingShare * R +
        (supportCount * (singletonMaxCapShare * R) + tailShare * R)
        =
          (remainingShare + (supportCount * singletonMaxCapShare + tailShare)) *
            R :=
          hrewrite
    _ < 1 * R := hscaled
    _ = D - paid := by
      simp [R]

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
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
  let supportCount : ℝ :=
    ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
        n Ωnz v true true true 1).card : ℝ)
  let remaining :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
      β H n Ωnz v
  let singletonMaxCap :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
      β H n Ωnz v hv
  let tail :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
      β H n Ωnz v
  have hscalar : remaining + (supportCount * singletonMaxCap + tail) < R := by
    simpa [remaining, singletonMaxCap, tail, supportCount, R, Ωnz, cap, D, paid]
      using hn H hH Ω v hv
  have hremainingNonneg : 0 ≤ remaining := by
    simpa [remaining] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have hsingletonNonneg : 0 ≤ singletonMaxCap := by
    simpa [singletonMaxCap] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz hv
  have htailNonneg : 0 ≤ tail := by
    simpa [tail] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  have hcountNonneg : 0 ≤ supportCount := by
    exact Nat.cast_nonneg _
  have hlhsNonneg : 0 ≤ remaining + (supportCount * singletonMaxCap + tail) := by
    exact
      add_nonneg hremainingNonneg
        (add_nonneg (mul_nonneg hcountNonneg hsingletonNonneg) htailNonneg)
  have hRpos : 0 < R := lt_of_le_of_lt hlhsNonneg hscalar
  refine
    ⟨remaining / R, singletonMaxCap / R, tail / R,
      hRpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg hremainingNonneg (le_of_lt hRpos)
  · exact div_nonneg hsingletonNonneg (le_of_lt hRpos)
  · exact div_nonneg htailNonneg (le_of_lt hRpos)
  · change remaining ≤ (remaining / R) * R
    exact le_of_eq (by field_simp [hRpos.ne'])
  · change singletonMaxCap ≤ (singletonMaxCap / R) * R
    exact le_of_eq (by field_simp [hRpos.ne'])
  · change tail ≤ (tail / R) * R
    exact le_of_eq (by field_simp [hRpos.ne'])
  · change remaining / R + (supportCount * (singletonMaxCap / R) + tail / R) < 1
    have hscalar' : remaining + supportCount * singletonMaxCap + tail < R := by
      simpa [add_assoc] using hscalar
    have hratio :
        remaining / R + (supportCount * singletonMaxCap) / R + tail / R < 1 :=
      (three_ratio_sum_lt_one_iff_sum_lt_of_pos
        (one := remaining)
        (boundary := supportCount * singletonMaxCap)
        (empty := tail)
        hRpos).2 hscalar'
    have hrewrite :
        remaining / R + (supportCount * (singletonMaxCap / R) + tail / R) =
          remaining / R + (supportCount * singletonMaxCap) / R + tail / R := by
      ring
    simpa [hrewrite] using hratio

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFreeAbsorption_iff_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFree :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical :=
  ⟨fun h =>
      boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFree
        (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFree
          h),
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFree⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
  exact
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFree
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFree
        h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
  exact
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFree
      (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSupportCountTailStrictRemainderDenominatorFree
        h)

end Exact3D
end StatMech
