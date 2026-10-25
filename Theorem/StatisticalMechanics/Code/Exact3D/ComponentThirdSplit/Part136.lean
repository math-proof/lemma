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
import Abbrev.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part12
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThird_of_uncutoff
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let capSmall :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ωnz
  let capLarge :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω
  let oneTerm := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hcapLe : capSmall ≤ capLarge := by
    simpa [capSmall, capLarge, Ωnz] using
      boundaryCrossingCapSourceSectorMultiplicitySquareBound_weightNonzeroCutoff_le
        β H Ω
  have honeTerm : 0 ≤ oneTerm := by
    simpa [oneTerm] using
      boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg hβpos hH
  have hmul : capSmall * oneTerm ≤ capLarge * oneTerm :=
    mul_le_mul_of_nonneg_right hcapLe honeTerm
  have hlarge : capLarge * oneTerm ≤ D / 3 := by
    simpa [capLarge, oneTerm, D] using hn H hH Ω v hv
  exact le_trans hmul hlarge

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThird_of_uncutoff
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let capSmall :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ωnz
  let capLarge :=
    boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω
  let boundaryTerm := boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
    β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hcapLe : capSmall ≤ capLarge := by
    simpa [capSmall, capLarge, Ωnz] using
      boundaryCrossingCapSourceSectorMultiplicitySquareBound_weightNonzeroCutoff_le
        β H Ω
  have hboundaryTerm : 0 ≤ boundaryTerm := by
    simpa [boundaryTerm] using
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
        v hβpos hH
  have hmul : capSmall * boundaryTerm ≤ capLarge * boundaryTerm :=
    mul_le_mul_of_nonneg_right hcapLe hboundaryTerm
  have hlarge : capLarge * boundaryTerm ≤ D / 3 := by
    simpa [capLarge, boundaryTerm, D] using hn H hH Ω v hv
  exact le_trans hmul hlarge

set_option linter.style.longLine false in


theorem boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSumWithBound_mono
    boundaryCrossingCapBoundLe_pairCountMultiplicity_sourceSectorMultiplicitySquare
    hsum

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_uncutoffCombined
      h)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareCombinedEmptyShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_combinedEmptyShare
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareComponentShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_componentShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareCapBudgetUncutoff
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_capBudgetUncutoff
      h)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareCapBudgetScheduleUncutoff
    {capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
        capBudget) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_capBudgetScheduleUncutoff
      h)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryScalar
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalarPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_aggregateEnvelopeActualBoundaryScalar
      h)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryTwoThird_emptyThird
    (haggregate :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryScalar
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalar_of_twoThird_emptyThird
      haggregate hempty)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeExactPolynomialBoundaryPositiveRatioResidualBudgets_emptyThird
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryTwoThird_emptyThird
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_exactPolynomialBoundaryPositiveRatioResidualBudgets
      hone hboundary)
    hempty

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryComponents_emptyThird
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryTwoThird_emptyThird
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_components
      hone hboundary)
    hempty

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryCardSourceBoundaryEdge_emptyCoefficientPositiveRatio
    {oneCardBudget boundaryCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {oneSourceCardBudget boundarySourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule}
    {oneEdgeMultiplicityBudget boundaryEdgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule}
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
        oneCardBudget oneSourceCardBudget oneEdgeMultiplicityBudget)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
        boundaryCardBudget boundarySourceCardBudget
        boundaryEdgeMultiplicityBudget)
    (hpay :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPositiveRatioPaymentPositiveSubcritical
        q)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        q) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryTwoThird_emptyThird
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_of_cardSourceBoundaryEdgeBudgetSchedules
      hone hboundary)
    (boxRatioEmptyBoundaryThird_of_coefficientPositiveRatioPayment_sourcePairRatioComparison
      hpay hcmp)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryCardSourceBoundaryEdge_emptyCoefficientPositiveRatio
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdCardSourceBoundaryEdgeBudgetSchedule_of_actualSchedulePayment
      hone)
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdCardSourceBoundaryEdgeBudgetSchedule_of_actualSchedulePayment
      hboundary)
    boxRatioEmptyBoundaryCoefficientPositiveRatioPayment_allowedSourcePairBudget
    hcmp

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeExactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePayment_of_exactPolynomialBoundaryActualSchedulePayment
      hone)
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePayment_of_exactPolynomialBoundaryActualSchedulePayment
      hboundary)
    hcmp

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopePolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePayment_of_polynomialBoundaryActualSchedulePayment
      hone)
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePayment_of_polynomialBoundaryActualSchedulePayment
      hboundary)
    hcmp

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_of_components
      hone hboundary hempty)


theorem boundaryCrossingCapComponentThirdsAbsorption_of_components
    (hone : BoundaryCrossingCapOnePointThirdPositiveSubcritical)
    (hboundary : BoundaryCrossingCapBoundaryPairThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc, hboundary β hβpos hβc,
    hempty β hβpos hβc] with n hnone hnboundary hnempty
  intro H hH Ω v hv
  exact ⟨hnone H hH Ω v hv, hnboundary H hH Ω v hv,
    hnempty H hH Ω v hv⟩


theorem boundaryCrossingCapOnePointThird_of_capBound
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapOnePointThirdWithBoundPositiveSubcritical capBound) :
    BoundaryCrossingCapOnePointThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcap β hβpos hβc, hone β hβpos hβc] with
    n hncap hnone
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let cap' := capBound β H n Ωnz
  let term := finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
    β H n
  have hcaple : cap ≤ cap' := by
    simpa [cap, cap', Ωnz] using hncap H hH Ω
  have hterm : 0 ≤ term := by
    simpa [term] using
      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_nonneg
        (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH)
  calc
    cap * term ≤ cap' * term :=
      mul_le_mul_of_nonneg_right hcaple hterm
    _ ≤ finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v / 3 := by
      simpa [cap', Ωnz, term] using hnone H hH Ω v hv


theorem boundaryCrossingCapBoundaryPairThird_of_capBound
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hboundary :
      BoundaryCrossingCapBoundaryPairThirdWithBoundPositiveSubcritical
        capBound) :
    BoundaryCrossingCapBoundaryPairThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcap β hβpos hβc, hboundary β hβpos hβc] with
    n hncap hnboundary
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let cap' := capBound β H n Ωnz
  let term := finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
    β H n v
  have hcaple : cap ≤ cap' := by
    simpa [cap, cap', Ωnz] using hncap H hH Ω
  have hterm : 0 ≤ term := by
    simpa [term] using
      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_nonneg
        (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH) v
  calc
    cap * term ≤ cap' * term :=
      mul_le_mul_of_nonneg_right hcaple hterm
    _ ≤ finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v / 3 := by
      simpa [cap', Ωnz, term] using hnboundary H hH Ω v hv


theorem onePointBoxRatioCurrentRatioThird_of_capBound
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound) :
    BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcap β hβpos hβc, hone β hβpos hβc] with
    n hncap hnone
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let cap' := capBound β H n Ωnz
  let term := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  have hcaple : cap ≤ cap' := by
    simpa [cap, cap', Ωnz] using hncap H hH Ω
  have hterm : 0 ≤ term := by
    simpa [term] using
      boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg
        (β := β) (H := H) (n := n) hβpos hH
  calc
    cap * term ≤ cap' * term :=
      mul_le_mul_of_nonneg_right hcaple hterm
    _ ≤ boundaryVertexBoxSimonCurrentRatio β n v / 3 := by
      simpa [cap', Ωnz, term] using hnone H hH Ω v hv


theorem boundaryPairBoxRatioCurrentRatioThird_of_capBound
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound) :
    BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcap β hβpos hβc, hboundary β hβpos hβc] with
    n hncap hnboundary
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let cap' := capBound β H n Ωnz
  let term :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  have hcaple : cap ≤ cap' := by
    simpa [cap, cap', Ωnz] using hncap H hH Ω
  have hterm : 0 ≤ term := by
    simpa [term] using
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
        (β := β) (H := H) (n := n) v hβpos hH
  calc
    cap * term ≤ cap' * term :=
      mul_le_mul_of_nonneg_right hcaple hterm
    _ ≤ boundaryVertexBoxSimonCurrentRatio β n v / 3 := by
      simpa [cap', Ωnz, term] using hnboundary H hH Ω v hv

set_option linter.style.longLine false in


theorem onePointBoxRatioCurrentRatioThird_of_sourceSectorMultiplicitySquare
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical :=
  onePointBoxRatioCurrentRatioThird_of_capBound
    boundaryCrossingCapUpperBound_sourceSectorMultiplicitySquare hone

set_option linter.style.longLine false in


theorem boundaryPairBoxRatioCurrentRatioThird_of_sourceSectorMultiplicitySquare
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical :=
  boundaryPairBoxRatioCurrentRatioThird_of_capBound
    boundaryCrossingCapUpperBound_sourceSectorMultiplicitySquare hboundary


theorem boundaryCrossingCapBoxRatioComponentShare_of_capBound
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcap β hβpos hβc, hshare β hβpos hβc] with
    n hncap hnshare
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let cap' := capBound β H n Ωnz
  rcases hnshare H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare,
      honeShare, hboundaryShare, hemptyShare, hshareSum,
      hone, hboundary, hempty⟩
  refine
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare,
      honeShare, hboundaryShare, hemptyShare, hshareSum, ?_, ?_,
      hempty⟩
  · let term := boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
    have hcaple : cap ≤ cap' := by
      simpa [cap, cap', Ωnz] using hncap H hH Ω
    have hterm : 0 ≤ term := by
      simpa [term] using
        boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg
          (β := β) (H := H) (n := n) hβpos hH
    calc
      cap * term ≤ cap' * term :=
        mul_le_mul_of_nonneg_right hcaple hterm
      _ ≤ oneShare * boundaryVertexBoxSimonCurrentRatio β n v := by
        simpa [cap', Ωnz, term] using hone
  · let term :=
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
    have hcaple : cap ≤ cap' := by
      simpa [cap, cap', Ωnz] using hncap H hH Ω
    have hterm : 0 ≤ term := by
      simpa [term] using
        boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
          (β := β) (H := H) (n := n) v hβpos hH
    calc
      cap * term ≤ cap' * term :=
        mul_le_mul_of_nonneg_right hcaple hterm
      _ ≤ boundaryPairShare * boundaryVertexBoxSimonCurrentRatio β n v := by
        simpa [cap', Ωnz, term] using hboundary

set_option linter.style.longLine false in


theorem boundaryCrossingCapBoxRatioComponentShare_of_sourceSectorMultiplicitySquare
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentShare_of_capBound
    boundaryCrossingCapUpperBound_sourceSectorMultiplicitySquare hshare


theorem boundaryCrossingCapBoxRatioComponentShare_of_boxRatioComponents
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc, hboundary β hβpos hβc,
    hempty β hβpos hβc] with n hnone hnboundary hnempty
  intro H hH Ω v hv
  refine
    ⟨1 / 3, 1 / 3, 1 / 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc]
      using hnone H hH Ω v hv
  · simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc]
      using hnboundary H hH Ω v hv
  · simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc]
      using hnempty H hH Ω v hv


theorem
    boundaryCrossingCapBoxRatioComponentShareWithBound_of_boxRatioComponentsWithBound
    {capBound : BoundaryCrossingCapBound}
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
      capBound := by
  intro β hβpos hβc
  filter_upwards [hone β hβpos hβc, hboundary β hβpos hβc,
    hempty β hβpos hβc] with n hnone hnboundary hnempty
  intro H hH Ω v hv
  refine
    ⟨1 / 3, 1 / 3, 1 / 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc]
      using hnone H hH Ω v hv
  · simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc]
      using hnboundary H hH Ω v hv
  · simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc]
      using hnempty H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentShare_of_sourceSectorMultiplicitySquareComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentShare_of_sourceSectorMultiplicitySquare
    (boundaryCrossingCapBoxRatioComponentShareWithBound_of_boxRatioComponentsWithBound
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem boundaryCrossingCapBoxRatioComponentShareWithBound_of_componentSumWithBound
    {capBound : BoundaryCrossingCapBound}
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
      capBound := by
  intro β hβpos hβc
  filter_upwards [hcapNonneg β hβpos hβc, hsum β hβpos hβc] with
    n hncap hnsum
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := capBound β H n Ωnz
  let one :=
    cap * boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n
  let boundary :=
    cap *
      boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm β H n v
  let empty := boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
    β H n v
  let D := boundaryVertexBoxSimonCurrentRatio β n v
  have hD : 0 ≤ D := by
    simpa [D] using
      boundaryVertexBoxSimonCurrentRatio_nonneg
        (β := β) (n := n) v (le_of_lt hβpos)
  have hcap : 0 ≤ cap := by
    simpa [cap, Ωnz] using hncap H hH Ω
  have honeTerm :
      0 ≤ boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n :=
    boundaryVertexTanhNormalizedOnePointCurrentRatioTerm_nonneg hβpos hH
  have hboundaryTerm :
      0 ≤ boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
        β H n v :=
    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm_nonneg
      v hβpos hH
  have hemptyTerm :
      0 ≤ boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
        β H n v :=
    boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm_nonneg
      v hβpos hH
  have hone : 0 ≤ one := by
    exact mul_nonneg hcap honeTerm
  have hboundary : 0 ≤ boundary := by
    exact mul_nonneg hcap hboundaryTerm
  have hempty : 0 ≤ empty := hemptyTerm
  have hsum' : one + boundary + empty ≤ D := by
    simpa [one, boundary, empty, D, cap, Ωnz] using hnsum H hH Ω v hv
  rcases componentShares_of_nonneg_sum_le hD hone hboundary hempty hsum' with
    ⟨oneShare, boundaryShare, emptyShare, honeShare, hboundaryShare,
      hemptyShare, hshareSum, honeLe, hboundaryLe, hemptyLe⟩
  exact
    ⟨oneShare, boundaryShare, emptyShare, honeShare, hboundaryShare,
      hemptyShare, hshareSum,
      by simpa [one, D, cap, Ωnz] using honeLe,
      by simpa [boundary, D, cap, Ωnz] using hboundaryLe,
      by simpa [empty, D] using hemptyLe⟩

set_option linter.style.longLine false in


theorem boundaryCrossingCapBoxRatioComponentShare_of_componentSum
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical := by
  have hbounded :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        boundaryCrossingCapPairCountMultiplicityBound :=
    boundaryCrossingCapBoxRatioComponentShareWithBound_of_componentSumWithBound
      boundaryCrossingCapBoundNonnegative_pairCountMultiplicity hsum
  simpa [
    BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical,
    BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical,
    boundaryCrossingCapPairCountMultiplicityBound,
    boundaryCrossingCap] using hbounded

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShare_of_componentSum
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentShareWithBound_of_componentSumWithBound
    boundaryCrossingCapBoundNonnegative_sourceSectorMultiplicitySquare hsum

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShare_of_componentShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical :=
  boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShare_of_componentSum
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSum_of_componentShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapBoxRatioComponentShare_of_sourceSectorMultiplicitySquareComponentSum
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical :=
  boundaryCrossingCapBoxRatioComponentShare_of_componentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
      hsum)


theorem onePointThird_of_tanhNormalizedOnePointThird
    (h :
      BoundaryCrossingCapTanhNormalizedOnePointThirdPositiveSubcritical) :
    BoundaryCrossingCapOnePointThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  exact
    onePointThird_of_tanhNormalizedOnePointThird_pointwise
      hβpos hH hv cap (by simpa [cap, Ωnz] using hn H hH Ω v hv)


theorem boundaryPairThird_of_tanhNormalizedBoundaryPairThird
    (h :
      BoundaryCrossingCapTanhNormalizedBoundaryPairThirdPositiveSubcritical) :
    BoundaryCrossingCapBoundaryPairThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  exact
    boundaryPairThird_of_tanhNormalizedBoundaryPairThird_pointwise
      hβpos hH hv cap (by simpa [cap, Ωnz] using hn H hH Ω v hv)


theorem tanhNormalizedOnePointThird_of_currentRatioThird
    (h :
      BoundaryCrossingCapTanhNormalizedOnePointCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapTanhNormalizedOnePointThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  have hcurrent :
      cap * boundaryVertexTanhNormalizedOnePointCurrentTerm β H n ≤
        boundaryVertexTanhNormalizedSimonCurrentDenominator β H n v / 3 :=
    tanhNormalizedOnePointCurrentThird_of_ratioThird_pointwise
      cap (by simpa [cap, Ωnz] using hn H hH Ω v hv)
  simpa [
    boundaryVertexTanhNormalizedOnePointTerm_eq_currentTerm,
    boundaryVertexTanhNormalizedSimonDenominator_eq_currentDenominator]
    using hcurrent


theorem tanhNormalizedBoundaryPairThird_of_currentRatioThird
    (h :
      BoundaryCrossingCapTanhNormalizedBoundaryPairCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapTanhNormalizedBoundaryPairThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  have hcurrent :
      cap * boundaryVertexTanhNormalizedBoundaryPairCurrentTerm β H n v ≤
        boundaryVertexTanhNormalizedSimonCurrentDenominator β H n v / 3 :=
    tanhNormalizedBoundaryPairCurrentThird_of_ratioThird_pointwise
      cap (by simpa [cap, Ωnz] using hn H hH Ω v hv)
  simpa [
    boundaryVertexTanhNormalizedBoundaryPairTerm_eq_currentTerm,
    boundaryVertexTanhNormalizedSimonDenominator_eq_currentDenominator]
    using hcurrent


theorem onePointThird_of_tanhNormalizedOnePointCurrentRatioThird
    (h :
      BoundaryCrossingCapTanhNormalizedOnePointCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapOnePointThirdPositiveSubcritical :=
  onePointThird_of_tanhNormalizedOnePointThird
    (tanhNormalizedOnePointThird_of_currentRatioThird h)


theorem boundaryPairThird_of_tanhNormalizedBoundaryPairCurrentRatioThird
    (h :
      BoundaryCrossingCapTanhNormalizedBoundaryPairCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapBoundaryPairThirdPositiveSubcritical :=
  boundaryPairThird_of_tanhNormalizedBoundaryPairThird
    (tanhNormalizedBoundaryPairThird_of_currentRatioThird h)


theorem onePointCurrentRatioThird_of_boxRatioThird
    (h :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapTanhNormalizedOnePointCurrentRatioThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  exact
    tanhNormalizedOnePointCurrentRatioThird_of_boxRatioThird_pointwise
      hv cap (by simpa [cap, Ωnz] using hn H hH Ω v hv)


theorem boundaryPairCurrentRatioThird_of_boxRatioThird
    (h :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapTanhNormalizedBoundaryPairCurrentRatioThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  exact
    tanhNormalizedBoundaryPairCurrentRatioThird_of_boxRatioThird_pointwise
      hv cap (by simpa [cap, Ωnz] using hn H hH Ω v hv)


theorem onePointThird_of_boxRatioCurrentRatioThird
    (h :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapOnePointThirdPositiveSubcritical :=
  onePointThird_of_tanhNormalizedOnePointCurrentRatioThird
    (onePointCurrentRatioThird_of_boxRatioThird h)


theorem boundaryPairThird_of_boxRatioCurrentRatioThird
    (h :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapBoundaryPairThirdPositiveSubcritical :=
  boundaryPairThird_of_tanhNormalizedBoundaryPairCurrentRatioThird
    (boundaryPairCurrentRatioThird_of_boxRatioThird h)


theorem emptyBoundaryThird_of_tanhNormalizedEmptyBoundaryThird
    (h :
      BoundaryCrossingCapTanhNormalizedEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapEmptyBoundaryThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  exact
    emptyBoundaryThird_of_tanhNormalizedEmptyBoundaryThird_pointwise
      hβpos hH hv (hn H hH Ω v hv)


theorem tanhNormalizedEmptyBoundaryThird_of_currentRatioThird
    (h :
      BoundaryCrossingCapTanhNormalizedEmptyBoundaryCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapTanhNormalizedEmptyBoundaryThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  have hcurrent :
      boundaryVertexTanhNormalizedEmptyBoundaryCurrentTerm β H n v ≤
        boundaryVertexTanhNormalizedSimonCurrentDenominator β H n v / 3 :=
    tanhNormalizedEmptyBoundaryCurrentThird_of_ratioThird_pointwise
      (hn H hH Ω v hv)
  simpa [
    boundaryVertexTanhNormalizedEmptyBoundaryTerm_eq_currentTerm,
    boundaryVertexTanhNormalizedSimonDenominator_eq_currentDenominator]
    using hcurrent


theorem emptyBoundaryThird_of_tanhNormalizedEmptyBoundaryCurrentRatioThird
    (h :
      BoundaryCrossingCapTanhNormalizedEmptyBoundaryCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapEmptyBoundaryThirdPositiveSubcritical :=
  emptyBoundaryThird_of_tanhNormalizedEmptyBoundaryThird
    (tanhNormalizedEmptyBoundaryThird_of_currentRatioThird h)


theorem currentRatioThird_of_boxRatioThird
    (h : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapTanhNormalizedEmptyBoundaryCurrentRatioThirdPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  exact
    tanhNormalizedEmptyBoundaryCurrentRatioThird_of_boxRatioThird_pointwise
      hv (hn H hH Ω v hv)


theorem emptyBoundaryThird_of_boxRatioEmptyBoundaryThird
    (h : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapEmptyBoundaryThirdPositiveSubcritical :=
  emptyBoundaryThird_of_tanhNormalizedEmptyBoundaryCurrentRatioThird
    (currentRatioThird_of_boxRatioThird h)


theorem boundaryCrossingCapComponentShareAbsorption_of_boxRatioComponentShare
    (h : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    BoundaryCrossingCapComponentSharePositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare,
      honeShare, hboundaryShare, hemptyShare, hshareSum,
      hone, hboundary, hempty⟩
  refine
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare,
      honeShare, hboundaryShare, hemptyShare, hshareSum, ?_, ?_, ?_⟩
  · have honeOriginal :
        cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
            β H n ≤
          oneShare * finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
            β H n v :=
      onePointShare_of_boxRatioCurrentRatioShare_pointwise
        hβpos hH hv cap oneShare (by simpa [cap, Ωnz] using hone)
    simpa [boundaryCrossingCap, cap, Ωnz] using honeOriginal
  · have hboundaryOriginal :
        cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v ≤
          boundaryPairShare *
            finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v :=
      boundaryPairShare_of_boxRatioCurrentRatioShare_pointwise
        hβpos hH hv cap boundaryPairShare
        (by simpa [cap, Ωnz] using hboundary)
    simpa [boundaryCrossingCap, cap, Ωnz] using hboundaryOriginal
  · exact
      emptyBoundaryShare_of_boxRatioCurrentRatioShare_pointwise
        hβpos hH hv emptyBoundaryShare hempty


theorem boundaryCrossingCapComponentShareAbsorption_of_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    BoundaryCrossingCapComponentSharePositiveSubcritical :=
  boundaryCrossingCapComponentShareAbsorption_of_boxRatioComponentShare
    (boundaryCrossingCapBoxRatioComponentShare_of_capBound hcap hshare)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapComponentShareAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    BoundaryCrossingCapComponentSharePositiveSubcritical :=
  boundaryCrossingCapComponentShareAbsorption_of_boxRatioComponentShare
    (boundaryCrossingCapBoxRatioComponentShare_of_sourceSectorMultiplicitySquare
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapComponentShareAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    BoundaryCrossingCapComponentSharePositiveSubcritical :=
  boundaryCrossingCapComponentShareAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShare_of_componentSum
      hsum)


theorem boundaryCrossingCapComponentThirdsAbsorption_of_components_tanhNormalizedEmpty
    (hone : BoundaryCrossingCapOnePointThirdPositiveSubcritical)
    (hboundary : BoundaryCrossingCapBoundaryPairThirdPositiveSubcritical)
    (hempty :
      BoundaryCrossingCapTanhNormalizedEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical :=
  boundaryCrossingCapComponentThirdsAbsorption_of_components
    hone hboundary
    (emptyBoundaryThird_of_tanhNormalizedEmptyBoundaryThird hempty)


theorem boundaryCrossingCapComponentThirdsAbsorption_of_tanhNormalizedComponents
    (hone :
      BoundaryCrossingCapTanhNormalizedOnePointThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapTanhNormalizedBoundaryPairThirdPositiveSubcritical)
    (hempty :
      BoundaryCrossingCapTanhNormalizedEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical :=
  boundaryCrossingCapComponentThirdsAbsorption_of_components_tanhNormalizedEmpty
    (onePointThird_of_tanhNormalizedOnePointThird hone)
    (boundaryPairThird_of_tanhNormalizedBoundaryPairThird hboundary)
    hempty


theorem boundaryCrossingCapComponentThirdsAbsorption_of_components_currentRatioEmpty
    (hone : BoundaryCrossingCapOnePointThirdPositiveSubcritical)
    (hboundary : BoundaryCrossingCapBoundaryPairThirdPositiveSubcritical)
    (hempty :
      BoundaryCrossingCapTanhNormalizedEmptyBoundaryCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical :=
  boundaryCrossingCapComponentThirdsAbsorption_of_components
    hone hboundary
    (emptyBoundaryThird_of_tanhNormalizedEmptyBoundaryCurrentRatioThird hempty)


theorem boundaryCrossingCapComponentThirdsAbsorption_of_tanhNormalizedComponents_currentRatioEmpty
    (hone :
      BoundaryCrossingCapTanhNormalizedOnePointThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapTanhNormalizedBoundaryPairThirdPositiveSubcritical)
    (hempty :
      BoundaryCrossingCapTanhNormalizedEmptyBoundaryCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical :=
  boundaryCrossingCapComponentThirdsAbsorption_of_components_currentRatioEmpty
    (onePointThird_of_tanhNormalizedOnePointThird hone)
    (boundaryPairThird_of_tanhNormalizedBoundaryPairThird hboundary)
    hempty


theorem boundaryCrossingCapComponentThirdsAbsorption_of_currentRatioComponents
    (hone :
      BoundaryCrossingCapTanhNormalizedOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapTanhNormalizedBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty :
      BoundaryCrossingCapTanhNormalizedEmptyBoundaryCurrentRatioThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical :=
  boundaryCrossingCapComponentThirdsAbsorption_of_tanhNormalizedComponents_currentRatioEmpty
    (tanhNormalizedOnePointThird_of_currentRatioThird hone)
    (tanhNormalizedBoundaryPairThird_of_currentRatioThird hboundary)
    hempty


theorem boundaryCrossingCapComponentThirdsAbsorption_of_components_boxRatioEmpty
    (hone : BoundaryCrossingCapOnePointThirdPositiveSubcritical)
    (hboundary : BoundaryCrossingCapBoundaryPairThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical :=
  boundaryCrossingCapComponentThirdsAbsorption_of_components
    hone hboundary
    (emptyBoundaryThird_of_boxRatioEmptyBoundaryThird hempty)


theorem boundaryCrossingCapComponentThirdsAbsorption_of_tanhNormalizedComponents_boxRatioEmpty
    (hone :
      BoundaryCrossingCapTanhNormalizedOnePointThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapTanhNormalizedBoundaryPairThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical :=
  boundaryCrossingCapComponentThirdsAbsorption_of_components_boxRatioEmpty
    (onePointThird_of_tanhNormalizedOnePointThird hone)
    (boundaryPairThird_of_tanhNormalizedBoundaryPairThird hboundary)
    hempty


theorem boundaryCrossingCapComponentThirdsAbsorption_of_currentRatioComponents_boxRatioEmpty
    (hone :
      BoundaryCrossingCapTanhNormalizedOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapTanhNormalizedBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical :=
  boundaryCrossingCapComponentThirdsAbsorption_of_tanhNormalizedComponents_boxRatioEmpty
    (tanhNormalizedOnePointThird_of_currentRatioThird hone)
    (tanhNormalizedBoundaryPairThird_of_currentRatioThird hboundary)
    hempty


theorem boundaryCrossingCapComponentThirdsAbsorption_of_boxRatioComponents
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical :=
  boundaryCrossingCapComponentThirdsAbsorption_of_currentRatioComponents_boxRatioEmpty
    (onePointCurrentRatioThird_of_boxRatioThird hone)
    (boundaryPairCurrentRatioThird_of_boxRatioThird hboundary)
    hempty


theorem boundaryCrossingCapComponentThirdsAbsorption_of_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical :=
  boundaryCrossingCapComponentThirdsAbsorption_of_boxRatioComponents
    (onePointBoxRatioCurrentRatioThird_of_capBound hcap hone)
    (boundaryPairBoxRatioCurrentRatioThird_of_capBound hcap hboundary)
    hempty

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapComponentThirdsAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical :=
  boundaryCrossingCapComponentThirdsAbsorption_of_capBound_boxRatioComponents
    boundaryCrossingCapUpperBound_sourceSectorMultiplicitySquare
    hone hboundary hempty

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapComponentThirdsAbsorption_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical :=
  boundaryCrossingCapComponentThirdsAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThird_of_uncutoff
      hone)
    (boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThird_of_uncutoff
      hboundary)
    hempty


theorem boundaryCrossingCapComponentThirdsAbsorption_of_capBound_boxRatioEmpty
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapOnePointThirdWithBoundPositiveSubcritical capBound)
    (hboundary :
      BoundaryCrossingCapBoundaryPairThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical :=
  boundaryCrossingCapComponentThirdsAbsorption_of_components_boxRatioEmpty
    (boundaryCrossingCapOnePointThird_of_capBound hcap hone)
    (boundaryCrossingCapBoundaryPairThird_of_capBound hcap hboundary)
    hempty


theorem boundaryCrossingCapCappedComponentBudget_of_componentThirdsAbsorption
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    BoundaryCrossingCapCappedBudgetPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hn H hH Ω v hv with ⟨hone, hboundary, hempty⟩
  refine ⟨D / 3, D / 3, D / 3, hone, hboundary, hempty, ?_⟩
  exact le_of_eq (by ring)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapCappedComponentBudget_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapCappedBudgetPositiveSubcritical :=
  boundaryCrossingCapCappedComponentBudget_of_componentThirdsAbsorption
    (boundaryCrossingCapComponentThirdsAbsorption_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
      hone hboundary hempty)


theorem boundaryCrossingCapComponentShareAbsorption_of_componentThirdsAbsorption
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    BoundaryCrossingCapComponentSharePositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with ⟨hone, hboundary, hempty⟩
  refine
    ⟨1 / 3, 1 / 3, 1 / 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · simpa [boundaryCrossingCap, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using hone
  · simpa [boundaryCrossingCap, div_eq_mul_inv, mul_comm, mul_left_comm,
      mul_assoc] using hboundary
  · simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hempty

set_option linter.style.longLine false in


theorem boundaryCrossingCapCappedComponentBudget_of_componentShareAbsorption
    (h : BoundaryCrossingCapComponentSharePositiveSubcritical) :
    BoundaryCrossingCapCappedBudgetPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
    h


theorem boundaryCrossingCapComponentShareAbsorption_of_boxRatioComponents
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentSharePositiveSubcritical :=
  boundaryCrossingCapComponentShareAbsorption_of_boxRatioComponentShare
    (boundaryCrossingCapBoxRatioComponentShare_of_boxRatioComponents
      hone hboundary hempty)


theorem boundaryCrossingCapComponentShareAbsorption_of_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentSharePositiveSubcritical :=
  boundaryCrossingCapComponentShareAbsorption_of_capBound_boxRatioComponentShare
    hcap
    (boundaryCrossingCapBoxRatioComponentShareWithBound_of_boxRatioComponentsWithBound
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapComponentShareAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentSharePositiveSubcritical :=
  boundaryCrossingCapComponentShareAbsorption_of_capBound_boxRatioComponents
    boundaryCrossingCapUpperBound_sourceSectorMultiplicitySquare
    hone hboundary hempty

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapComponentShareAbsorption_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentSharePositiveSubcritical :=
  boundaryCrossingCapComponentShareAbsorption_of_componentThirdsAbsorption
    (boundaryCrossingCapComponentThirdsAbsorption_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_componentShare_componentThirdsAbsorption
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
    (boundaryCrossingCapComponentShareAbsorption_of_componentThirdsAbsorption h)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_boxRatioComponentShare
    (h : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
    (boundaryCrossingCapComponentShareAbsorption_of_boxRatioComponentShare h)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_boxRatioComponentSum
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentShare
    (boundaryCrossingCapBoxRatioComponentShare_of_componentSum hsum)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
    (boundaryCrossingCapComponentShareAbsorption_of_capBound_boxRatioComponentShare
      hcap hshare)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_capBound_boxRatioComponentShare
    boundaryCrossingCapUpperBound_sourceSectorMultiplicitySquare hshare

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
      hsum)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareComponentShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareCapBudgetUncutoff
      h)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff
    {capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
        capBudget) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareCapBudgetScheduleUncutoff
      h)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalar
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalarPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryScalar
      h)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_emptyThird
    (haggregate :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryTwoThird_emptyThird
      haggregate hempty)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryPositiveRatioResidualBudgets_emptyThird
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeExactPolynomialBoundaryPositiveRatioResidualBudgets_emptyThird
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryCardSourceBoundaryEdge_emptyCoefficientPositiveRatio
    {oneCardBudget boundaryCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {oneSourceCardBudget boundarySourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule}
    {oneEdgeMultiplicityBudget boundaryEdgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule}
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
        oneCardBudget oneSourceCardBudget oneEdgeMultiplicityBudget)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
        boundaryCardBudget boundarySourceCardBudget
        boundaryEdgeMultiplicityBudget)
    (hpay :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPositiveRatioPaymentPositiveSubcritical
        q)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        q) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryCardSourceBoundaryEdge_emptyCoefficientPositiveRatio
      hone hboundary hpay hcmp)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeExactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopePolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryComponents_emptyThird
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryComponents_emptyThird
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_boxRatioComponents
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_boxRatioComponentShare
    (boundaryCrossingCapBoxRatioComponentShare_of_boxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_capBound_boxRatioComponentShare hcap
    (boundaryCrossingCapBoxRatioComponentShareWithBound_of_boxRatioComponentsWithBound
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_capBound_boxRatioComponents
    boundaryCrossingCapUpperBound_sourceSectorMultiplicitySquare
    hone hboundary hempty


theorem firstExitPositive_of_componentShare_componentThirdsAbsorption
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_componentShare_componentThirdsAbsorption h)


theorem firstExitPositive_of_boxRatioComponentShare
    (h : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_boxRatioComponentShare h)

set_option linter.style.longLine false in


theorem firstExitPositive_of_boxRatioComponentSum
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_boxRatioComponentSum hsum)


theorem firstExitPositive_of_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_capBound_boxRatioComponentShare hcap hshare)

set_option linter.style.longLine false in


theorem firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
      hsum)

set_option linter.style.longLine false in


theorem firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff
      h)

set_option linter.style.longLine false in


theorem firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff
    {capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
        capBudget) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff
      h)

set_option linter.style.longLine false in


theorem firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalar
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalarPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalar
      h)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_emptyThird
    (haggregate :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_emptyThird
      haggregate hempty)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryPositiveRatioResidualBudgets_emptyThird
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryPositiveRatioResidualBudgets_emptyThird
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryCardSourceBoundaryEdge_emptyCoefficientPositiveRatio
    {oneCardBudget boundaryCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {oneSourceCardBudget boundarySourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule}
    {oneEdgeMultiplicityBudget boundaryEdgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule}
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
        oneCardBudget oneSourceCardBudget oneEdgeMultiplicityBudget)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
        boundaryCardBudget boundarySourceCardBudget
        boundaryEdgeMultiplicityBudget)
    (hpay :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPositiveRatioPaymentPositiveSubcritical
        q)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        q) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryCardSourceBoundaryEdge_emptyCoefficientPositiveRatio
      hone hboundary hpay hcmp)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryComponents_emptyThird
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryComponents_emptyThird
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
      hone hboundary hempty)


theorem firstExitPositive_of_boxRatioComponents
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_boxRatioComponents hone hboundary hempty)


theorem firstExitPositive_of_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)

set_option linter.style.longLine false in


theorem firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)


theorem boundaryGhostComparison_of_componentShare_componentThirdsAbsorption
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (firstExitPositive_of_componentShare_componentThirdsAbsorption h)


theorem boundaryGhostComparison_of_boxRatioComponentShare
    (h : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (firstExitPositive_of_boxRatioComponentShare h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_boxRatioComponentSum
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (firstExitPositive_of_boxRatioComponentSum hsum)


theorem boundaryGhostComparison_of_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (firstExitPositive_of_capBound_boxRatioComponentShare hcap hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
      hsum)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareComponentShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareCapBudgetUncutoff
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff
    {capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
        capBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareCapBudgetScheduleUncutoff
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalar
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryScalarPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryScalar
      h)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThird_emptyThird
    (haggregate :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryTwoThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryTwoThird_emptyThird
      haggregate hempty)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryPositiveRatioResidualBudgets_emptyThird
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointPositiveRatioResidualBudgetPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairPositiveRatioResidualBudgetPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeExactPolynomialBoundaryPositiveRatioResidualBudgets_emptyThird
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryCardSourceBoundaryEdge_emptyCoefficientPositiveRatio
    {oneCardBudget boundaryCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule}
    {oneSourceCardBudget boundarySourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule}
    {oneEdgeMultiplicityBudget boundaryEdgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule}
    {q : BoundaryCrossingCapBoxRatioEmptyBoundarySourcePairBudget}
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
        oneCardBudget oneSourceCardBudget oneEdgeMultiplicityBudget)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdCardSourceBoundaryEdgeBudgetSchedulePositiveSubcritical
        boundaryCardBudget boundarySourceCardBudget
        boundaryEdgeMultiplicityBudget)
    (hpay :
      BoundaryCrossingCapBoxRatioEmptyBoundaryCoefficientPositiveRatioPaymentPositiveSubcritical
        q)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        q) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryCardSourceBoundaryEdge_emptyCoefficientPositiveRatio
      hone hboundary hpay hcmp)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeExactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopePolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryComponents_emptyThird
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryComponents_emptyThird
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffComponents
      hone hboundary hempty)


theorem boundaryGhostComparison_of_boxRatioComponents
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (firstExitPositive_of_boxRatioComponents hone hboundary hempty)


theorem boundaryGhostComparison_of_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (firstExitPositive_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)


theorem boundaryCrossingCapComponentSumAbsorption_of_componentThirdsAbsorption
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_cappedComponentBudget
    (boundaryCrossingCapCappedComponentBudget_of_componentThirdsAbsorption h)


theorem boundaryCrossingCapComponentSumAbsorption_of_componentShareAbsorption
    (h : BoundaryCrossingCapComponentSharePositiveSubcritical) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_cappedComponentBudget
    (boundaryCrossingCapCappedComponentBudget_of_componentShareAbsorption h)


theorem boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentShare
    (h : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_componentShareAbsorption
    (boundaryCrossingCapComponentShareAbsorption_of_boxRatioComponentShare h)


theorem boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_componentShareAbsorption
    (boundaryCrossingCapComponentShareAbsorption_of_capBound_boxRatioComponentShare
      hcap hshare)

set_option linter.style.longLine false in


theorem boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentShare
    hcap
    (boundaryCrossingCapBoxRatioComponentShareWithBound_of_componentSumWithBound
      hcapNonneg hsum)

set_option linter.style.longLine false in


theorem boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentSum
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentSum
    boundaryCrossingCapUpperBound_pairCountMultiplicity
    boundaryCrossingCapBoundNonnegative_pairCountMultiplicity
    hsum

set_option linter.style.longLine false in


theorem boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponents
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_componentThirdsAbsorption
    (boundaryCrossingCapComponentThirdsAbsorption_of_boxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_componentThirdsAbsorption
    (boundaryCrossingCapComponentThirdsAbsorption_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderNonnegative_of_boxRatioComponentSum
    (h :
      BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderNonnegativePositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderNonnegative_of_boundaryCrossingCapComponentSum
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentSum h)

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorption_of_boxRatioComponentSum_remainderShare
    (hcomponent :
      BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorption_of_remainderNonnegative_remainderShare
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderNonnegative_of_boxRatioComponentSum
      hcomponent)
    hshare

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareBoxRatioComponentSum
    (hcomponent :
      BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainder
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorption_of_boxRatioComponentSum_remainderShare
      hcomponent hshare)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_componentShareAbsorption
    (boundaryCrossingCapComponentShareAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
      hsum)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentThirdsAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_componentThirdsAbsorption h)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceComponentMajorization_componentThirdsAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_componentThirdsAbsorption h)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceComponentMajorization_componentThirdsAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_componentThirdsAbsorption h)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentThirdsAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_componentThirdsAbsorption h)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentShare
      hcap hshare)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceComponentMajorization_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentShare
      hcap hshare)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceComponentMajorization_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentShare
      hcap hshare)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceComponentMajorization_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentShare
      hcap hshare)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentSum
      hcap hcapNonneg hsum)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceComponentMajorization_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentSum
      hcap hcapNonneg hsum)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceComponentMajorization_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentSum
      hcap hcapNonneg hsum)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceComponentMajorization_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentSum
      hcap hcapNonneg hsum)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_boxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceComponentMajorization_boxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceComponentMajorization_boxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceComponentMajorization_boxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceComponentMajorization_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceComponentMajorization_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceComponentMajorization_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_boxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceComponentMajorization_boxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceComponentMajorization_boxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceComponentMajorization_boxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_boxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceComponentMajorization_boxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceComponentMajorization_boxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceComponentMajorization_boxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapComponentSumPositiveSubcritical :=
  boundaryCrossingCapComponentSumAbsorption_of_componentShareAbsorption
    (boundaryCrossingCapComponentShareAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceComponentMajorization_sourceSectorMultiplicitySquareBoxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceComponentMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceComponentMajorization_componentSum
    hmajor
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)


theorem positiveDenominatorComponentSumAbsorption_of_boxGeometry_componentThirdsAbsorption
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    BoundaryCrossingCapPositiveDenominatorComponentSumPositiveSubcritical :=
  finiteQ2PositiveDenominatorComponentSumAbsorption_of_boxGeometry_componentSumAbsorption
    (boundaryCrossingCapComponentSumAbsorption_of_componentThirdsAbsorption h)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxGeometry_componentThirdsAbsorption
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (positiveDenominatorComponentSumAbsorption_of_boxGeometry_componentThirdsAbsorption
      h)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boxGeometry_componentThirdsAbsorption
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (positiveDenominatorComponentSumAbsorption_of_boxGeometry_componentThirdsAbsorption
      h)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_boxGeometry_componentThirdsAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxGeometry_componentThirdsAbsorption
      h)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_decrementedSourceProfileMajorization_boxGeometry_componentThirdsAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxGeometry_componentThirdsAbsorption
      h)

set_option linter.style.longLine false in


theorem firstExitPositive_of_decrementedSourceProfileMajorization_boxGeometry_componentThirdsAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxGeometry_componentThirdsAbsorption
      h)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxGeometry_componentThirdsAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxGeometry_componentThirdsAbsorption
      h)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponents
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxGeometry_componentThirdsAbsorption
    (boundaryCrossingCapComponentThirdsAbsorption_of_boxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boxRatioComponents
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boxGeometry_componentThirdsAbsorption
    (boundaryCrossingCapComponentThirdsAbsorption_of_boxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_boxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_boxGeometry_componentThirdsAbsorption
    hmajor
    (boundaryCrossingCapComponentThirdsAbsorption_of_boxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_decrementedSourceProfileMajorization_boxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_boxGeometry_componentThirdsAbsorption
    hmajor
    (boundaryCrossingCapComponentThirdsAbsorption_of_boxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem firstExitPositive_of_decrementedSourceProfileMajorization_boxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_boxGeometry_componentThirdsAbsorption
    hmajor
    (boundaryCrossingCapComponentThirdsAbsorption_of_boxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxGeometry_componentThirdsAbsorption
    hmajor
    (boundaryCrossingCapComponentThirdsAbsorption_of_boxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxGeometry_componentThirdsAbsorption
    (boundaryCrossingCapComponentThirdsAbsorption_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boxGeometry_componentThirdsAbsorption
    (boundaryCrossingCapComponentThirdsAbsorption_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_boxGeometry_componentThirdsAbsorption
    hmajor
    (boundaryCrossingCapComponentThirdsAbsorption_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_decrementedSourceProfileMajorization_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_boxGeometry_componentThirdsAbsorption
    hmajor
    (boundaryCrossingCapComponentThirdsAbsorption_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)

set_option linter.style.longLine false in


theorem firstExitPositive_of_decrementedSourceProfileMajorization_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_boxGeometry_componentThirdsAbsorption
    hmajor
    (boundaryCrossingCapComponentThirdsAbsorption_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_decrementedSourceProfileMajorization_capBound_boxRatioComponents
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxGeometry_componentThirdsAbsorption
    hmajor
    (boundaryCrossingCapComponentThirdsAbsorption_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)


theorem positiveDenominatorComponentSumAbsorption_of_boxGeometry_boxRatioComponentShare
    (h : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    BoundaryCrossingCapPositiveDenominatorComponentSumPositiveSubcritical :=
  finiteQ2PositiveDenominatorComponentSumAbsorption_of_boxGeometry_componentSumAbsorption
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentShare h)

set_option linter.style.longLine false in


theorem positiveDenominatorComponentSumAbsorption_of_boxGeometry_boxRatioComponentSum
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    BoundaryCrossingCapPositiveDenominatorComponentSumPositiveSubcritical :=
  finiteQ2PositiveDenominatorComponentSumAbsorption_of_boxGeometry_componentSumAbsorption
    (boundaryCrossingCapComponentSumAbsorption_of_boxRatioComponentSum hsum)


theorem
    positiveDenominatorComponentSumAbsorption_of_boxGeometry_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    BoundaryCrossingCapPositiveDenominatorComponentSumPositiveSubcritical :=
  finiteQ2PositiveDenominatorComponentSumAbsorption_of_boxGeometry_componentSumAbsorption
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentShare
      hcap hshare)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (positiveDenominatorComponentSumAbsorption_of_boxGeometry_capBound_boxRatioComponentShare
      hcap hshare)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (positiveDenominatorComponentSumAbsorption_of_boxGeometry_capBound_boxRatioComponentShare
      hcap hshare)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_capBound_boxRatioComponentShare
      hcap hshare)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_decrementedSourceProfileMajorization_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_capBound_boxRatioComponentShare
      hcap hshare)

set_option linter.style.longLine false in


theorem firstExitPositive_of_decrementedSourceProfileMajorization_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_capBound_boxRatioComponentShare
      hcap hshare)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_decrementedSourceProfileMajorization_capBound_boxRatioComponentShare
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_capBound_boxRatioComponentShare
      hcap hshare)

set_option linter.style.longLine false in


theorem positiveDenominatorComponentSumAbsorption_of_boxGeometry_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    BoundaryCrossingCapPositiveDenominatorComponentSumPositiveSubcritical :=
  finiteQ2PositiveDenominatorComponentSumAbsorption_of_boxGeometry_componentSumAbsorption
    (boundaryCrossingCapComponentSumAbsorption_of_capBound_boxRatioComponentSum
      hcap hcapNonneg hsum)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_capBound_boxRatioComponentShare hcap
    (boundaryCrossingCapBoxRatioComponentShareWithBound_of_componentSumWithBound
      hcapNonneg hsum)

set_option linter.style.longLine false in


theorem firstExitPositive_of_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_capBound_boxRatioComponentSum
      hcap hcapNonneg hsum)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (firstExitPositive_of_capBound_boxRatioComponentSum
      hcap hcapNonneg hsum)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (positiveDenominatorComponentSumAbsorption_of_boxGeometry_capBound_boxRatioComponentSum
      hcap hcapNonneg hsum)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (positiveDenominatorComponentSumAbsorption_of_boxGeometry_capBound_boxRatioComponentSum
      hcap hcapNonneg hsum)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_capBound_boxRatioComponentSum
      hcap hcapNonneg hsum)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_decrementedSourceProfileMajorization_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_capBound_boxRatioComponentSum
      hcap hcapNonneg hsum)

set_option linter.style.longLine false in


theorem firstExitPositive_of_decrementedSourceProfileMajorization_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_capBound_boxRatioComponentSum
      hcap hcapNonneg hsum)

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_decrementedSourceProfileMajorization_capBound_boxRatioComponentSum
    {capBound : BoundaryCrossingCapBound}
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_capBound_boxRatioComponentSum
      hcap hcapNonneg hsum)

set_option linter.style.longLine false in


theorem
    positiveDenominatorComponentSumAbsorption_of_boxGeometry_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    BoundaryCrossingCapPositiveDenominatorComponentSumPositiveSubcritical :=
  finiteQ2PositiveDenominatorComponentSumAbsorption_of_boxGeometry_componentSumAbsorption
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    positiveDenominatorComponentSumAbsorption_of_boxGeometry_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    BoundaryCrossingCapPositiveDenominatorComponentSumPositiveSubcritical :=
  positiveDenominatorComponentSumAbsorption_of_boxGeometry_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
      hsum)

set_option linter.style.longLine false in


theorem
    positiveDenominatorComponentSumAbsorption_of_boxGeometry_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    BoundaryCrossingCapPositiveDenominatorComponentSumPositiveSubcritical :=
  positiveDenominatorComponentSumAbsorption_of_boxGeometry_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem
    positiveDenominatorComponentSumAbsorption_of_boxGeometry_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    BoundaryCrossingCapPositiveDenominatorComponentSumPositiveSubcritical :=
  positiveDenominatorComponentSumAbsorption_of_boxGeometry_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentShare
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (positiveDenominatorComponentSumAbsorption_of_boxGeometry_boxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boxRatioComponentShare
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (positiveDenominatorComponentSumAbsorption_of_boxGeometry_boxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentShare
    (boundaryCrossingCapBoxRatioComponentShare_of_sourceSectorMultiplicitySquare
      hshare)

set_option linter.style.longLine false in


theorem
    finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boxRatioComponentShare
    (boundaryCrossingCapBoxRatioComponentShare_of_sourceSectorMultiplicitySquare
      hshare)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentSum
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (positiveDenominatorComponentSumAbsorption_of_boxGeometry_boxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boxRatioComponentSum
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (positiveDenominatorComponentSumAbsorption_of_boxGeometry_boxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem
    finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
      hsum)

set_option linter.style.longLine false in


theorem
    finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
      hsum)

set_option linter.style.longLine false in


theorem
    finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem
    finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem
    finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_boxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceProfileMajorization_boxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceProfileMajorization_boxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentShare
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_boxRatioComponentShare
    hmajor
    (boundaryCrossingCapBoxRatioComponentShare_of_sourceSectorMultiplicitySquare
      hshare)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_boxRatioComponentShare
    hmajor
    (boundaryCrossingCapBoxRatioComponentShare_of_sourceSectorMultiplicitySquare
      hshare)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_boxRatioComponentShare
    hmajor
    (boundaryCrossingCapBoxRatioComponentShare_of_sourceSectorMultiplicitySquare
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxRatioComponentShare
    hmajor
    (boundaryCrossingCapBoxRatioComponentShare_of_sourceSectorMultiplicitySquare
      hshare)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boxRatioComponentSum
      hsum)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalExpandedDemand_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    (boundaryVertexDecrementedSourceProfileMajorization_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
      (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand
        hrawStrict hmixed))
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalFiniteAtomCharge_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteAtomChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalExpandedDemand_actualSchedulePayments_allowedEmptyComparison
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedFiniteAtomCharge
      hmixed)
    hone hboundary hcmp

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalFiniteInjectionCharge_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalExpandedDemand_actualSchedulePayments_allowedEmptyComparison
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedFiniteInjectionCharge
      hmixed)
    hone hboundary hcmp

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalFiniteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalExpandedDemand_actualSchedulePayments_allowedEmptyComparison
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemand_of_unpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionCharge
      hmixed)
    hone hboundary hcmp

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdScalar_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    (boundaryVertexDecrementedSourceProfileMajorization_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
      (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge
        hrawStrict hthreshold))
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRankedPrefix_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hranked :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdScalar_actualSchedulePayments_allowedEmptyComparison
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge
      hranked)
    hone hboundary hcmp

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalSortedAtomSlot_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hsorted :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRankedPrefix_actualSchedulePayments_allowedEmptyComparison
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotCharge
      hsorted)
    hone hboundary hcmp

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hinjection :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalSortedAtomSlot_actualSchedulePayments_allowedEmptyComparison
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge
      hinjection)
    hone hboundary hcmp

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotHall_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hhall :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge
      hhall)
    hone hboundary hcmp

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hcapacityHall :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotHall_actualSchedulePayments_allowedEmptyComparison
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge
      hcapacityHall)
    hone hboundary hcmp

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCharge
      hthreshold)
    hone hboundary hcmp

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hdisjoint :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointCharge
      hdisjoint)
    hone hboundary hcmp

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdInjection_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdScalar_actualSchedulePayments_allowedEmptyComparison
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge
      hthreshold)
    hone hboundary hcmp

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdInjection_actualSchedulePayments_allowedEmptyComparison
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge
      hthreshold)
    hone hboundary hcmp

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hthreshold :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison
    hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingCharge
      hthreshold)
    hone hboundary hcmp

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    hmajor
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
      hsum)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    hmajor
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
      hsum)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    hmajor
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
      hsum)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    hmajor
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquare
      hsum)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    hmajor
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    hmajor
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    hmajor
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    hmajor
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffCombined
      h)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    hmajor
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    hmajor
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    hmajor
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxRatioComponentSum
    hmajor
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    positiveDenominatorComponentSumAbsorption_of_boxGeometry_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapPositiveDenominatorComponentSumPositiveSubcritical :=
  positiveDenominatorComponentSumAbsorption_of_boxGeometry_boxRatioComponentSum
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareUncutoffComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    positiveDenominatorComponentSumAbsorption_of_boxGeometry_sourceSectorMultiplicitySquareBoxRatioComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    BoundaryCrossingCapPositiveDenominatorComponentSumPositiveSubcritical :=
  finiteQ2PositiveDenominatorComponentSumAbsorption_of_boxGeometry_componentSumAbsorption
    (boundaryCrossingCapComponentSumAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (positiveDenominatorComponentSumAbsorption_of_boxGeometry_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    finiteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (positiveDenominatorComponentSumAbsorption_of_boxGeometry_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical :=
  boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    finiteCutoffBound_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    firstExitPositive_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  firstExitPositive_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)

set_option linter.style.longLine false in


theorem
    boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponents
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    hmajor
    (finiteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)


theorem finiteCutoffBound_of_boxGeometry_componentThirdsAbsorption
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteCutoffBound_of_positiveDenominatorComponentSumAbsorption
    (positiveDenominatorComponentSumAbsorption_of_boxGeometry_componentThirdsAbsorption
      h)


theorem firstExitPositive_of_boxGeometry_componentThirdsAbsorption
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteCutoffBound_of_boxGeometry_componentThirdsAbsorption h)


theorem boundaryGhostComparison_of_boxGeometry_componentThirdsAbsorption
    (h : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (firstExitPositive_of_boxGeometry_componentThirdsAbsorption h)

end Exact3D
end StatMech
