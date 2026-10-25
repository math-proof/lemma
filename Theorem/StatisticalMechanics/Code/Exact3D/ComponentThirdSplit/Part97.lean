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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part102
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
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
  let R := D - paid
  let singletonOptionClassifiedCount : ℝ :=
    ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))).card : ℝ)
  rcases hn H hH Ω v hv with
    ⟨remainingShare, singletonMaxCapShare, tailShare, hRpos,
      _hremainingShareNonneg, _hsingletonShareNonneg, _htailShareNonneg,
      hremaining, hcapBound, htailBound, hshareStrict⟩
  refine
    ⟨remainingShare * R, singletonMaxCapShare * R, tailShare * R,
      hremaining, hcapBound, htailBound, ?_⟩
  have hscaled :
      (remainingShare +
            (singletonOptionClassifiedCount * singletonMaxCapShare +
              tailShare)) *
          R <
        1 * R :=
    mul_lt_mul_of_pos_right hshareStrict hRpos
  have hrewrite :
      remainingShare * R +
          (singletonOptionClassifiedCount * (singletonMaxCapShare * R) +
            tailShare * R) =
        (remainingShare +
            (singletonOptionClassifiedCount * singletonMaxCapShare +
              tailShare)) *
          R := by
    ring
  calc
    remainingShare * R +
        (singletonOptionClassifiedCount * (singletonMaxCapShare * R) +
          tailShare * R)
        =
          (remainingShare +
              (singletonOptionClassifiedCount * singletonMaxCapShare +
                tailShare)) *
            R :=
          hrewrite
    _ < 1 * R := hscaled
    _ = D - paid := by
      simp [R]

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
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
  let singletonOptionClassifiedCount : ℝ :=
    ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true
          ({x} : Finset (Option (FK.boxVerts 3 n)))).card : ℝ)
  let remaining :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
      β H n Ωnz v
  let singletonMaxCap :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
      β H n Ωnz v hv
  let tail :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
      β H n Ωnz v
  have hscalar :
      remaining + (singletonOptionClassifiedCount * singletonMaxCap + tail) <
        R := by
    simpa [remaining, singletonMaxCap, tail, singletonOptionClassifiedCount, R,
      Ωnz, cap, D, paid] using hn H hH Ω v hv
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
  have hcountNonneg : 0 ≤ singletonOptionClassifiedCount := by
    dsimp [singletonOptionClassifiedCount]
    exact Finset.sum_nonneg fun x _hx => Nat.cast_nonneg _
  have hlhsNonneg :
      0 ≤ remaining + (singletonOptionClassifiedCount * singletonMaxCap + tail) := by
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
  · change
      remaining / R +
          (singletonOptionClassifiedCount * (singletonMaxCap / R) + tail / R) <
        1
    have hscalar' :
        remaining + singletonOptionClassifiedCount * singletonMaxCap + tail <
          R := by
      simpa [add_assoc] using hscalar
    have hratio :
        remaining / R +
            (singletonOptionClassifiedCount * singletonMaxCap) / R +
            tail / R <
          1 :=
      (three_ratio_sum_lt_one_iff_sum_lt_of_pos
        (one := remaining)
        (boundary := singletonOptionClassifiedCount * singletonMaxCap)
        (empty := tail)
        hRpos).2 hscalar'
    have hrewrite :
        remaining / R +
            (singletonOptionClassifiedCount * (singletonMaxCap / R) +
              tail / R) =
          remaining / R +
              (singletonOptionClassifiedCount * singletonMaxCap) / R +
              tail / R := by
      ring
    simpa [hrewrite] using hratio

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_iff_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical ↔
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical :=
  ⟨fun h =>
      boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
        (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree
          h),
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentShareSingletonOptionClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSingletonOptionClassifiedCountTailStrictRemainderDenominatorFree⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapSupportCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
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
  let classifiedCount : ℝ :=
    ∑ R ∈
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v 1,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true R).card : ℝ)
  let singletonMaxCap :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
      β H n Ωnz v hv
  have hcountLe : supportCount ≤ classifiedCount := by
    simpa [supportCount, classifiedCount] using
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_card_cast_le_sum_residualCaseClassifiedSet_card
        Ωnz v true true true 1
  have hcapNonneg : 0 ≤ singletonMaxCap := by
    simpa [singletonMaxCap] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap_nonneg
        (le_of_lt hβpos) (le_of_lt hH) n Ωnz hv
  have hmul : supportCount * singletonMaxCap ≤ classifiedCount * singletonMaxCap :=
    mul_le_mul_of_nonneg_right hcountLe hcapNonneg
  have htail :
      supportCount * singletonMaxCap +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v ≤
        classifiedCount * singletonMaxCap +
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
          (classifiedCount * singletonMaxCap +
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
              β H n Ωnz v) :=
    add_le_add le_rfl htail
  exact
    lt_of_le_of_lt hmono
      (by
        simpa [Ωnz, cap, D, paid, supportCount, classifiedCount, singletonMaxCap]
          using hn H hH Ω v hv)

end Exact3D
end StatMech
