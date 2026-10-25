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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part146
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePayment_of_exactPolynomialBoundaryActualSchedulePayment
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hone β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_eq_exactPolynomialBoundaryBudget]
    with n hnpay hbudgetEq
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let exactBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change actualBudget * oneTerm ≤ D / 3
  have hactualEq : actualBudget = exactBudget := by
    simpa [actualBudget, exactBudget] using hbudgetEq Ωnz
  have hexactPay : exactBudget * oneTerm ≤ D / 3 := by
    simpa [Ωnz, exactBudget, oneTerm, D,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget] using
      hnpay H hH Ω v hv
  simpa [hactualEq] using hexactPay

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePayment_of_exactPolynomialBoundaryActualSchedulePayment
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hboundary β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_eq_exactPolynomialBoundaryBudget]
    with n hnpay hbudgetEq
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let exactBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change actualBudget * boundaryTerm ≤ D / 3
  have hactualEq : actualBudget = exactBudget := by
    simpa [actualBudget, exactBudget] using hbudgetEq Ωnz
  have hexactPay : exactBudget * boundaryTerm ≤ D / 3 := by
    simpa [Ωnz, exactBudget, boundaryTerm, D,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget] using
      hnpay H hH Ω v hv
  simpa [hactualEq] using hexactPay

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePayment_of_actualBoundaryActualSchedulePayment
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hone β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_eq_exactPolynomialBoundaryBudget]
    with n hnpay hbudgetEq
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let exactBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
      n Ωnz
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change exactBudget * oneTerm ≤ D / 3
  have hactualEq : actualBudget = exactBudget := by
    simpa [actualBudget, exactBudget] using hbudgetEq Ωnz
  have hactualPay : actualBudget * oneTerm ≤ D / 3 := by
    simpa [Ωnz, actualBudget, oneTerm, D,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget] using
      hnpay H hH Ω v hv
  simpa [← hactualEq] using hactualPay

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePayment_of_actualBoundaryActualSchedulePayment
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards
    [hboundary β hβpos hβc,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget_eventually_eq_exactPolynomialBoundaryBudget]
    with n hnpay hbudgetEq
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let actualBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget
      n Ωnz
  let exactBudget :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateExactPolynomialBoundaryBudget
      n Ωnz
  let boundaryTerm :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  change exactBudget * boundaryTerm ≤ D / 3
  have hactualEq : actualBudget = exactBudget := by
    simpa [actualBudget, exactBudget] using hbudgetEq Ωnz
  have hactualPay : actualBudget * boundaryTerm ≤ D / 3 := by
    simpa [Ωnz, actualBudget, boundaryTerm, D,
      boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateActualBoundaryBudget] using
      hnpay H hH Ω v hv
  simpa [← hactualEq] using hactualPay

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePayment_iff_actualBoundaryActualSchedulePayment :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePayment_of_exactPolynomialBoundaryActualSchedulePayment,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePayment_of_actualBoundaryActualSchedulePayment⟩

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePayment_iff_actualBoundaryActualSchedulePayment :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical ↔
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical :=
  ⟨boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePayment_of_exactPolynomialBoundaryActualSchedulePayment,
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePayment_of_actualBoundaryActualSchedulePayment⟩

end Exact3D
end StatMech
