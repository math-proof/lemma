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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part147
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePayment_of_polynomialBoundaryActualSchedulePayment
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hone β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_le_polynomialBoundaryBudget]
    with n hnpay hbudgetLe
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let polynomialBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregatePolynomialBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change actualBudget * oneTerm ≤ D / 3
  have hactualLe : actualBudget ≤ polynomialBudget := by
    simpa [actualBudget, polynomialBudget] using hbudgetLe Ωnz
  have htermNonneg : 0 ≤ oneTerm := by
    simpa [oneTerm] using
      boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg
        (β := β) (H := H) (n := n) hβpos hH
  have hpolyPay : polynomialBudget * oneTerm ≤ D / 3 := by
    simpa [Ωnz, polynomialBudget, oneTerm, D,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregatePolynomialBoundaryBudget] using
      hnpay H hH Ω v hv
  exact (mul_le_mul_of_nonneg_right hactualLe htermNonneg).trans hpolyPay

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePayment_of_polynomialBoundaryActualSchedulePayment
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hboundary β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_le_polynomialBoundaryBudget]
    with n hnpay hbudgetLe
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let polynomialBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregatePolynomialBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change actualBudget * boundaryTerm ≤ D / 3
  have hactualLe : actualBudget ≤ polynomialBudget := by
    simpa [actualBudget, polynomialBudget] using hbudgetLe Ωnz
  have htermNonneg : 0 ≤ boundaryTerm := by
    simpa [boundaryTerm] using
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
        (β := β) (H := H) (n := n) v hβpos hH
  have hpolyPay : polynomialBudget * boundaryTerm ≤ D / 3 := by
    simpa [Ωnz, polynomialBudget, boundaryTerm, D,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregatePolynomialBoundaryBudget] using
      hnpay H hH Ω v hv
  exact (mul_le_mul_of_nonneg_right hactualLe htermNonneg).trans hpolyPay

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePayment_of_onePointThird
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc] with n hnone
  intro H hH Ω v hv
  simpa using hnone H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThird_of_actualSchedulePayment
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc] with n hnone
  intro H hH Ω v hv
  simpa using hnone H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePayment_iff_onePointThird :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThird_of_actualSchedulePayment,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePayment_of_onePointThird⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePayment_of_boundaryPairThird
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hboundary β hβpos hβc] with n hnboundary
  intro H hH Ω v hv
  simpa using hnboundary H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThird_of_actualSchedulePayment
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hboundary β hβpos hβc] with n hnboundary
  intro H hH Ω v hv
  simpa using hnboundary H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePayment_iff_boundaryPairThird :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThird_of_actualSchedulePayment,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePayment_of_boundaryPairThird⟩

end Exact3D
end StatMech
