/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part136
import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentTheorem
import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BcEqIsing
import Theorem.StatisticalMechanics.Code.Ising.TransitionAssembly


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_actualSchedulePayments_allowedEmptyComparison
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcompare :
      FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      hcompare)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_actualSchedulePayments_allowedEmptyComparison
      hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_exactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
        hone hboundary hcmp))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_polynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_sourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryActualSchedulePayments_allowedEmptyComparison
        hone hboundary hcmp))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostFirstExitPositive
      hfirst)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boxGeometryComponentThirdsAbsorption_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hthirds :
      BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_boxGeometry_componentThirdsAbsorption hthirds)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boxRatioComponentShare_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_boxRatioComponentShare hshare)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boxRatioComponentSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_boxRatioComponentSum hsum)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_capBound_boxRatioComponentShare_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_capBound_boxRatioComponentShare hcap hshare)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_capBound_boxRatioComponentSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_capBound_boxRatioComponentSum hcap hcapNonneg hsum)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boxRatioComponentThirds_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boxGeometryComponentThirdsAbsorption_projection
    hlim hfixed
    (boundaryCrossingCapComponentThirdsAbsorption_of_boxRatioComponents
      hone hboundary hempty)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_capBound_boxRatioComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {capBound : BoundaryCrossingCapBound}
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical
        capBound)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boxGeometryComponentThirdsAbsorption_projection
    hlim hfixed
    (boundaryCrossingCapComponentThirdsAbsorption_of_capBound_boxRatioComponents
      hcap hone hboundary hempty)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponentShare
      hshare)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponentSum
      hsum)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
      hshare)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff
      hshare)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff_projection
    {capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
        capBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
      hone hboundary hempty)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim hfixed
    (firstExitPositive_of_sourceSectorMultiplicitySquareBoxRatioComponents
      hone hboundary hempty)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponents
      hmajor hone hboundary hempty)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare
      hmajor hshare)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum
      hmajor hsum)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined
      hmajor h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff
      hmajor hshare)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents
      hmajor hone hboundary hempty)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15CanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSum
        h))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSum
        h))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15ComponentDenominatorFreeSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorption
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShare_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorption
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareSchedule_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorptionPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorption
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareScheduleComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hbudget :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBudgetPositiveSubcritical
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
        shellBudgetShare)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleComponents
      hbudget hone hboundary hempty hshell)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainder_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainder
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderStrict_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrict
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorption
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSum
      hstrict hshare)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFree
        h))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleComponents_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hsingleton :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleSingletonPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleComponentsTailStrictRemainderDenominatorFree
        hremaining htail hsingleton hpayment))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingleton_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {budget : LiveSingletonOptionComponentBudgetSchedule}
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
        budget)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
        budget)
    (hpayment :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical
        budget)
    (hsingletonResidual :
      LiveSingletonOptionComponentBudgetScheduleResidualCaseShareBudgetPositiveSubcritical
        budget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonTailStrictRemainderDenominatorFree
        hremaining htail hpayment hsingletonResidual))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSign_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingletonResidual :
      LiveSingletonOptionShareScheduleResidualCaseSingletonPayment
        schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignTailStrictRemainderDenominatorFree
        hR hstrict hremaining htail hsingletonResidual))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSign_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hsingletonResidual :
      LiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativePayment
        schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSign_projection
    hlim hfixed hR hstrict hremaining htail
    (liveSingletonOptionShareScheduleResidualCaseSingletonPayment_of_denominatorNonnegativePayment
      hsingletonResidual)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPayment_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment
        schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsDerivedSignTailStrictRemainderDenominatorFreeNamedPayment
        (schedule := schedule)
        hR hstrict hremaining htail hpayment))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPayment_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {schedule : LiveSingletonOptionShareSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hstrict :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
        schedule)
    (hremaining :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical
        schedule)
    (htail :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical
        schedule)
    (hpayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment
        label schedule)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsDerivedSignTailStrictRemainderDenominatorFreeNamedPayment
        (schedule := schedule) (label := label)
        hR hstrict hremaining htail hpayment))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFree
        hR hraw))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositive_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_projection
    hlim hfixed
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
      hpos)
    hraw hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositive_projection
    hlim hfixed
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hraw hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotal_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
          label))
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalDerivedSignTailStrictRemainderDenominatorFree
        (label := label) hR hraw))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositive_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotal_projection
    hlim hfixed
    (label := label)
    (liveSingletonOptionShareScheduleRemainderPositive_of_boundaryCrossingRemainderPositive
      (schedule := liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical
        label)
      hpos)
    hraw hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical
        label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositive_projection
    hlim hfixed
    (label := label)
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositive_of_boundaryCrossingCapComponentStrictCanonicalRatioShareSum
      hpaid)
    hraw hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption
        (ι := ι) (label := label) h))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentMajorantSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentMajorantSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentSum_projection
    hlim hfixed
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption_of_canonicalRawRowDependentLabelBudget15ComponentMajorantSum
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentSum_projection
    hlim hfixed
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorption_of_boxGeometry_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum
      h)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentMajorantSum_projection
    hlim hfixed
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentMajorantSumAbsorption_of_boxGeometry_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSum
      h)
    hprojection

section CanonicalRawRowDependentLabelBudget15RemainderFacade

variable {ι :
  (n : ℕ) →
    FK.boxVerts 3 n →
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}

variable [∀ n v hasGhost hasOrigin hasEndpoint R,
  Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]

variable [∀ n v hasGhost hasOrigin hasEndpoint R,
  DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]

variable {label :
  ∀ {n : ℕ},
    Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
    (v : FK.boxVerts 3 n) →
    ∀ hasGhost hasOrigin hasEndpoint R,
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
        ι n v hasGhost hasOrigin hasEndpoint R}

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeRemainderPositive_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeRemainderPositive
      (ι := ι) (label := label) hpos hraw)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictSumPositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictSum
      (ι := ι) (label := label) hstrict hraw)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictShare_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictSharePositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictShare
      (ι := ι) (label := label) hstrict hraw)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictCanonicalRatioShareSum
      (ι := ι) (label := label) hstrict hraw)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawRemainderDenominatorFreeComponentStrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFreeAbsorptionPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawRemainderDenominatorFreeComponentStrictCanonicalRatioShareSum
      (ι := ι) (label := label) hstrict hraw)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderCanonicalRawRowRatioComponentStrictCanonicalRatioShareSum_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hrawRatio :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15CanonicalRatioShareSumPositiveSubcritical
        ι label)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed
    (boundaryGhostComparison_of_nonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderCanonicalRawRowRatioComponentStrictCanonicalRatioShareSum
      (ι := ι) (label := label) hstrict hrawRatio)
    hprojection

end CanonicalRawRowDependentLabelBudget15RemainderFacade

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hprofile :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
      (boundaryGhostComparison_of_decrementedSourceProfileMajorization_boxRatioComponentSum
        (boundaryVertexDecrementedSourceProfileMajorization_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
          hprofile)
    (boundaryCrossingCapBoxRatioComponentSum_of_sourceSectorMultiplicitySquareAggregateEnvelopeActualBoundaryActualSchedulePayments_allowedEmptyComparison
          hone hboundary hcmp)))
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePayment_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hrawPayment :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignRawProfilePayment
      hR hrawStrict hrawPayment)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_paidPlusProfileDominatesSimonPlusActive_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hdom :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalPaidPlusProfileDominatesSimonPlusActiveWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignPaidPlusProfileDominatesSimonPlusActive
      hrawStrict hdom)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_unpaidRemainderLeProfileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hslack :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlackWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeProfileSlack
      hrawStrict hslack)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_unpaidRemainderPlusActiveLeProfile_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprofile :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfileWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusActiveLeProfile
      hrawStrict hprofile)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_unpaidRemainderPlusCollapsedActiveImageLeProfile_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hcollapsed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfileWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedActiveImageLeProfile
      hrawStrict hcollapsed)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_targetMultiplicityMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (htarget :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmpty
      hrawStrict htarget)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_targetMultiplicityMainEmptySlackSplit_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hsplit :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplitWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplit
      hrawStrict hsplit)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boundaryMultiplicityAndImageWeightLeMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hslack :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusBoundaryMultiplicityAndImageWeightLeMainEmpty
      hrawStrict hslack)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmain :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityMainAndCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderPlusBoundaryMultiplicityMainAndImageWeightEmpty
      hrawStrict hmain)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hempty :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalCollapsedBoundaryMultiplicityMainAndUnpaidRemainderPlusCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignBoundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmpty
      hrawStrict hempty)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixed_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixed
      hrawStrict hmixed)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedDeficitNonpositive_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositiveWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositive
      hrawStrict hmixed)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedPaymentDominates_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmixed :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominatesWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitFallbackMixedPaymentDominates
      hrawStrict hmixed)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalExpandedDemand_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalFiniteAtomCharge_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalFiniteInjectionCharge_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalFiniteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hmixed hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdScalar_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRankedPrefix_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hranked hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalSortedAtomSlot_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hsorted hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hinjection hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotHall_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hhall hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hcapacityHall hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalCanonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hdisjoint hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdInjection_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freeQ2BoundaryProfileSimonFreeSum_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison
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
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (boundaryGhostComparison_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalThresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hranked hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hsorted hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hinjection hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalSlotSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hsubtypeInjection :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotSubtypeInjectionChargeWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionCharge_of_unpaidRemainderReservoirSplitFallbackMixedCanonicalSlotSubtypeInjectionCharge
      hsubtypeInjection)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_mainEmptyGapAllocation_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hallocation :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocationWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_canonicalSlotSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict
    (residualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotSubtypeInjectionCharge_of_unpaidRemainderLeCollapsedMainEmptyGapAllocation
      hallocation)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_mainEmptyGap_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hgap :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGap
      hrawStrict hgap)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_mainEmptyGapMassSplit_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmass :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainEmptyGapMassSplit
      hrawStrict hmass)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_unpaidRemainderNonpositive_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hnonpos :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderNonpositiveWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderNonpositive
      hrawStrict hnonpos)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_mainGapSum_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hmainGap :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainGapSumWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedMainGapSum
      hrawStrict hmainGap)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_emptyGap_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hemptyGap :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedEmptyGapWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderLeCollapsedEmptyGap
      hrawStrict hemptyGap)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_reservoirBranchCover_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCoverWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirBranchCover
      hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_reservoirBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchDisjunctionWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirBranchDisjunction
      hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_reservoirBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection
    {chooseBranch : UnpaidRemainderReservoirBranchSelector}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirBranchSelector
      (chooseBranch := chooseBranch) hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_reservoirSplitBranchCover_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchCover
      hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_reservoirSplitBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchDisjunction
      hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_reservoirSplitBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection
    {chooseBranch : UnpaidRemainderReservoirSplitBranchSelector}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
        chooseBranch)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchSelector
      (chooseBranch := chooseBranch) hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in

theorem freePosSubcriticalMassBridge_of_reservoirSplitBranchFirstTrueSelector_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hrawStrict :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hbranch :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical
        unpaidRemainderReservoirSplitBranchFirstTrueSelector)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
    (hcmp :
      BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalDerivedSignUnpaidRemainderReservoirSplitBranchFirstTrueSelector
      hrawStrict hbranch)
    hone hboundary hcmp hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hhall hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hcapacityHall hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hdisjoint hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)
    hprojection

set_option linter.style.longLine false in


theorem freePosSubcriticalMassBridge_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison_projection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
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
        boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FreePositiveSubcriticalMassBridge :=
  freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim hfixed
    (freeQ2BoundaryProfileSimonFreeSum_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison
      hrawStrict hthreshold hone hboundary hcmp)
    hprojection

end Exact3D
end StatMech
