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
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part18


namespace StatMech

namespace Exact3D

namespace FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


noncomputable def correlationLengthBridge
    (I : FiniteCurrentMassBridgeInputs) :
    FreePositiveSubcriticalCorrelationLengthBridge :=
  freePositiveSubcriticalCorrelationLengthBridge_of_massBridge I.massBridge

set_option linter.style.longLine false in


noncomputable def ofActualScheduleProjectionInputs
    (I : FiniteCurrentActualScheduleProjectionInputs) :
    FiniteCurrentMassBridgeInputs :=
  ⟨I.massBridge⟩

set_option linter.style.longLine false in


noncomputable def ofThresholdCandidateEmbeddingProjectionInputs
    (I : FiniteCurrentThresholdCandidateEmbeddingProjectionInputs) :
    FiniteCurrentMassBridgeInputs :=
  ⟨I.massBridge⟩

set_option linter.style.longLine false in


noncomputable def ofExpandedDemandProjectionInputs
    (I : FiniteCurrentExpandedDemandProjectionInputs) :
    FiniteCurrentMassBridgeInputs :=
  ⟨I.massBridge⟩

set_option linter.style.longLine false in


noncomputable def ofBoundaryGhostComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcomparison : FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection
    hlim hfixed hcomparison hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofProfileSlackActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hprofile hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofPaidPlusProfileDominatesSimonPlusActiveActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_paidPlusProfileDominatesSimonPlusActive_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hdom hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofUnpaidRemainderLeProfileSlackActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_unpaidRemainderLeProfileSlack_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hslack hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofUnpaidRemainderPlusActiveLeProfileActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_unpaidRemainderPlusActiveLeProfile_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hprofile hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofUnpaidRemainderPlusCollapsedActiveImageLeProfileActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_unpaidRemainderPlusCollapsedActiveImageLeProfile_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hcollapsed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofTargetMultiplicityMainEmptyActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_targetMultiplicityMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict htarget hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofTargetMultiplicityMainEmptySlackSplitActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_targetMultiplicityMainEmptySlackSplit_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hsplit hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofBoundaryMultiplicityAndImageWeightLeMainEmptyActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boundaryMultiplicityAndImageWeightLeMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hslack hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofBoundaryMultiplicityMainAndImageWeightEmptyActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmain hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofBoundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmptyActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hempty hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofReservoirSplitFallbackMixedActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixed_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofReservoirSplitFallbackMixedDeficitNonpositiveActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedDeficitNonpositive_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofReservoirSplitFallbackMixedPaymentDominatesActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedPaymentDominates_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofExpandedDemandActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofFiniteAtomChargeActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofFiniteInjectionChargeActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofFiniteSetInjectionChargeActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofScalarThresholdActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofRankedPrefixActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hranked hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofSortedAtomSlotActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hsorted hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofCanonicalSlotInjectionActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hinjection hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofCanonicalSlotSubtypeInjectionActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_canonicalSlotSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hsubtypeInjection hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofMainEmptyGapAllocationActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_mainEmptyGapAllocation_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hallocation hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofMainEmptyGapActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_mainEmptyGap_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hgap hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofMainEmptyGapMassSplitActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_mainEmptyGapMassSplit_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmass hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofUnpaidRemainderNonpositiveActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_unpaidRemainderNonpositive_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hnonpos hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofMainGapSumActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_mainGapSum_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hmainGap hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofEmptyGapActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_emptyGap_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hemptyGap hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofReservoirBranchCoverActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirBranchCover_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofReservoirBranchDisjunctionActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofReservoirBranchSelectorActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofReservoirSplitBranchCoverActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitBranchCover_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofReservoirSplitBranchDisjunctionActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofReservoirSplitBranchSelectorActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofReservoirSplitBranchFirstTrueSelectorActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_reservoirSplitBranchFirstTrueSelector_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofCanonicalSlotHallActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hhall hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofCanonicalSlotCapacityHallActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hcapacityHall hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofCanonicalSlotCapacityThresholdActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofCanonicalSlotCapacityDisjointActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hdisjoint hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofThresholdInjectionActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofThresholdSubtypeInjectionActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofThresholdCandidateEmbeddingActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofExactPolynomialBoundaryActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_exactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofPolynomialBoundaryActualSchedulePaymentsAllowedEmptyComparisonProjection
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_polynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection
    hlim hfixed hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofFreeFVQ2ExactRestrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2Exact_restrictedCylinderComparison
    hcmp hdecay⟩

set_option linter.style.longLine false in


noncomputable def ofFreeFVQ2SubexpRestrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2Subexp_restrictedCylinderComparison
    hcmp hdecay⟩

set_option linter.style.longLine false in


noncomputable def ofFreeFVQ2TwoSidedRestrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_restrictedCylinderComparison
    hcmp hdecay⟩

set_option linter.style.longLine false in


noncomputable def ofBoundaryGhostFirstExitPositiveProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hfirst hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofBoxGeometryComponentThirdsAbsorptionProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hthirds :
      BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boxGeometryComponentThirdsAbsorption_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hthirds hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofBoxRatioComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boxRatioComponentShare_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hshare hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofBoxRatioComponentSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boxRatioComponentSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hsum hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofCapBoundBoxRatioComponentShareProjection
    {capBound : BoundaryCrossingCapBound}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_capBound_boxRatioComponentShare_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hcap hshare hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofCapBoundBoxRatioComponentSumProjection
    {capBound : BoundaryCrossingCapBound}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hcapNonneg :
      BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
    (hsum :
      BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical
        capBound)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_capBound_boxRatioComponentSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hcap hcapNonneg hsum hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofBoxRatioComponentThirdsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_boxRatioComponentThirds_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hone hboundary hempty hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofCapBoundBoxRatioComponentsProjection
    {capBound : BoundaryCrossingCapBound}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_capBound_boxRatioComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hcap hone hboundary hempty hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hshare hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hsum hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hshare hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hshare hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffProjection
    {capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
        capBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hone hboundary hempty hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofSourceSectorMultiplicitySquareBoxRatioComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hone hboundary hempty hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hmajor hone hboundary hempty hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hmajor hshare hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hmajor hsum hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hmajor h hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hmajor hshare hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hmajor hone hboundary hempty hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualThresholdShellBudget15CanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15CanonicalRatioShareSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualThresholdShellBudget15StrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualThresholdShellBudget15ComponentDenominatorFreeSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15ComponentDenominatorFreeSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualThresholdShellBudget15AggregateComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShare_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualThresholdShellBudget15AggregateComponentShareScheduleProjection
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorptionPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareSchedule_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofResidualThresholdShellBudget15AggregateComponentShareScheduleComponentsProjection
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareScheduleComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hbudget hone hboundary hempty hshell hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualThresholdShellBudget15BoundaryCrossingRemainderProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainder_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualThresholdShellBudget15BoundaryCrossingRemainderStrictProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderStrict_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualThresholdShellBudget15StrictComponentDenominatorFreeSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in


noncomputable def
    ofResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hstrict hshare hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    h hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofLiveSingletonOptionComponentBudgetScheduleComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleComponents_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hremaining htail hsingleton hpayment hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofLiveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingleton_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hremaining htail hpayment hsingletonResidual hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofLiveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSign_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (schedule := schedule)
    hR hstrict hremaining htail hsingletonResidual hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofLiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSignProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSign_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (schedule := schedule)
    hR hstrict hremaining htail hsingletonResidual hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPaymentProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPayment_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (schedule := schedule)
    hR hstrict hremaining htail hpayment hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPaymentProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPayment_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (schedule := schedule) (label := label)
    hR hstrict hremaining htail hpayment hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePayment_actualSchedulePayments_allowedEmptyComparison_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hR hrawStrict hrawPayment hone hboundary hcmp hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hR hraw hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositiveProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositive_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hpos hraw hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hpaid hraw hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotal_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (label := label) hR hraw hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositiveProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositive_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (label := label) hpos hraw hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
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
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    (label := label) hpaid hraw hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofFiniteFKSimonFreeSumDoubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_doubledBoxPolynomialProjection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hfinite hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofFiniteIsingSimonDoubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteIsingSimon_doubledBoxPolynomialProjection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hSimon hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_profileDoubleScale
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hprofile⟩

set_option linter.style.longLine false in


noncomputable def ofSimonFreeSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hsimon : FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_simonFreeSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hsimon hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofFiniteFKSimonFreeSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hfinite hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofFiniteIsingSimonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteIsingSimon_projection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hSimon hprojection⟩

set_option linter.style.longLine false in


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_fullCoordinateComparisons_profileDoubleScale
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hfinite hstrict hdiag hprofile⟩

set_option linter.style.longLine false in


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteIsingSimon_fullCoordinateComparisons_profileDoubleScale
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hSimon hstrict hdiag hprofile⟩

set_option linter.style.longLine false in


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hone :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgePolynomialProjection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullOneEdgeDescent_profileDoubleScale
      hone hprofile)⟩

set_option linter.style.longLine false in


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hone :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgePolynomialProjection
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDoubledBoxPolynomialProjection_of_fullOneEdgeDescent_profileDoubleScale
      hone hprofile)⟩

set_option linter.style.longLine false in


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_coordinateCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_coordinateCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_local
      honeLocal)
    hprofile

set_option linter.style.longLine false in


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_local
      honeLocal)
    hprofile

set_option linter.style.longLine false in


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_coordinateCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_coordinateCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCases
      hstrictZ hdiagY hstrictY)
    hprofile

set_option linter.style.longLine false in


noncomputable def ofFiniteFKSimonFreeSumAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfiniteAt :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in Filter.atTop,
          FreeQ2BoundaryProfileFiniteFKSimonFreeSumAt β hβpos n)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofileAt :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in Filter.atTop,
          FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay
    (freeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical_of_eventually_at
      hfiniteAt)
    honeLocal
    (freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_at
      hprofileAt)

set_option linter.style.longLine false in


noncomputable def ofFiniteIsingSimonAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimonAt :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in Filter.atTop,
          FiniteQ2SimonFreeBoundaryIsingBoxAt β n)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofileAt :
      ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in Filter.atTop,
          FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    hlim hdecay
    (finiteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical_of_eventually_at
      hSimonAt)
    honeLocal
    (freeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical_of_eventually_at
      hprofileAt)

set_option linter.style.longLine false in


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
    hlim hdecay hfinite
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparison_of_fullPredecessorComparison
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical_of_local
        hstrictLocal))
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparison_of_fullPredecessorComparison
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical_of_local
        hdiagLocal))
    hprofile

set_option linter.style.longLine false in


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
    hlim hdecay hSimon
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparison_of_fullPredecessorComparison
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical_of_local
        hstrictLocal))
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparison_of_fullPredecessorComparison
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical_of_local
        hdiagLocal))
    hprofile

set_option linter.style.longLine false in


noncomputable def ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteFKSimonFreeSum_positiveXFaceOrderedWedgeCoordinateStepBranches
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hfinite hstrict hdiag⟩

set_option linter.style.longLine false in


noncomputable def ofFiniteIsingSimonPositiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_finiteIsingSimon_positiveXFaceOrderedWedgeCoordinateStepBranches
    hlim
    (freeQ2FixedInnerTwoSidedPositiveSubcritical_of_freeFVQ2TwoSided hdecay)
    hSimon hstrict hdiag⟩

set_option linter.style.longLine false in


noncomputable def ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_finiteVolumePolynomialComparisonToXAxis
    hlim hdecay hcompare⟩

set_option linter.style.longLine false in


noncomputable def ofFreeFVQ2TwoSidedPolynomialRateWithXAxisLogRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hrate :
      FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_polynomialRateWithXAxisLogRate
    hlim hdecay hrate⟩

set_option linter.style.longLine false in


noncomputable def ofFreeFVQ2TwoSidedDirectionalRate
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_directionalRate
    hlim hdecay hdir⟩

set_option linter.style.longLine false in


noncomputable def ofFreeFVQ2TwoSidedConvexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_convexSurfaceTensionUpper
    hlim hdecay htension⟩

set_option linter.style.longLine false in


noncomputable def ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
    FiniteCurrentMassBridgeInputs :=
  ⟨freePosSubcriticalMassBridge_of_freeFVQ2TwoSided_actualConvexSurfaceTensionUpper
    hlim hdecay htension⟩

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree I.massBridge hpower

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_asymptoticPowerLaw
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAsymptoticPowerLaw
    C hagree I.massBridge hasymp

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_logAffine
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogAffineNearCritical
    C hagree I.massBridge hlog

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_logRatioLimit
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioLimit
    C hagree I.massBridge hratio

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_logRatioSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioSandwich
    C hagree I.massBridge hsand

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_powerSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassPowerSandwich
    C hagree I.massBridge hpow

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerUpper
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerUpper
    C hagree I.massBridge hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooExistsLowerUpper
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooExistsLowerUpper
    C hagree I.massBridge hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsUpperExists
    C hagree I.massBridge hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree I.massBridge hβc hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkBetaCLowerBoundExistsNoWindowUpperExists
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCLowerBoundExistsNoWindowUpperExists
    C hagree I.massBridge hβeq hβc hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkBetaCIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCIooSandwich
    C hagree I.massBridge hβeq hβc hsand

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkBetaCIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  I.freeMassPowerLawToPlusTarget_of_fkBetaCIooSandwich
    C hagree hβeq hβc (hsand.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCPullbackIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCPullbackIooSandwich
    C hagree I.massBridge hβeq hβc hpull

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCPullbackIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  I.freeMassPowerLawToPlusTarget_of_fkPCPullbackIooSandwich
    C hagree hβeq hβc (hpull.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCCanonicalWindowPullbackIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCCanonicalWindowPullbackIooSandwich
    C hagree I.massBridge hβeq hβc hcanon

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCCanonicalWindowPullbackIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  I.freeMassPowerLawToPlusTarget_of_fkPCCanonicalWindowPullbackIooSandwich
    C hagree hβeq hβc (hcanon.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedIooSandwich
    C hagree I.massBridge hβeq hβc hp

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  I.freeMassPowerLawToPlusTarget_of_fkPCSelectedIooSandwich
    C hagree hβeq hβc (hp.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpper
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLowerUpper
    C hagree I.massBridge hβeq hβc hselected hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpperExists
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLowerUpperExists
    C hagree I.massBridge hβeq hβc hselected hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpper_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        D hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        D hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  I.freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpper
    C hagree hβeq hβc hselected
    (hlower.congr_predictedExponent hpred)
    (hupper.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpperExists_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        D hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        D hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  I.freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpperExists
    C hagree hβeq hβc hselected
    (hlower.congr_predictedExponent hpred)
    (hupper.congr_predictedExponent hpred)

end FiniteCurrentMassBridgeInputs
end Exact3D
end StatMech
