/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part136
public import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part7
public import Theorem.StatisticalMechanics.Code.Exact3D.ExponentTheorem
public import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.BcEqIsing
public import Theorem.StatisticalMechanics.Code.Ising.TransitionAssembly
public import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent


public section

namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


structure FiniteCurrentThresholdCandidateEmbeddingProjectionInputs where
  thermodynamicLimit : FreeIsingThermodynamicLimitPositiveSubcritical
  fixedInner : FreeQ2FixedInnerTwoSidedPositiveSubcritical
  rawStrict :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical
  thresholdCandidateEmbedding :
    LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical
  onePointPayment :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical
  boundaryPairPayment :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical
  emptyComparison :
    BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical
      boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget
  projection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical

end Exact3D
end StatMech
