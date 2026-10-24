import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent
open StatMech StatMech.Exact3D StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs StatMech.Exact3D.FiniteCurrentThresholdCandidateEmbeddingProjectionInputs StatMech.Exact3D.FiniteCurrentExpandedDemandProjectionInputs StatMech.Exact3D.Ising3DTransitionAssemblyInputs StatMech.Exact3D.FiniteCurrentMassBridgeInputs


/--
[freeQ2BoundaryProfileSimonFreeSum_of_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_actualSchedulePayments_allowedEmptyComparison hone hboundary hcmp

/--
[freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcompare : FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_boundaryGhostComparison_projection hlim hfixed hcompare hprojection

/--
[freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_exactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_exactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeExactPolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_exactPolynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_polynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_polynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopePolynomialBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_polynomialBoundaryActualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hfirst : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_boundaryGhostFirstExitPositive_projection hlim hfixed hfirst hprojection

/--
[freePosSubcriticalMassBridge_of_boxGeometryComponentThirdsAbsorption_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_boxGeometryComponentThirdsAbsorption_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hthirds : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_boxGeometryComponentThirdsAbsorption_projection hlim hfixed hthirds hprojection

/--
[freePosSubcriticalMassBridge_of_boxRatioComponentShare_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_boxRatioComponentShare_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_boxRatioComponentShare_projection hlim hfixed hshare hprojection

/--
[freePosSubcriticalMassBridge_of_boxRatioComponentSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_boxRatioComponentSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_boxRatioComponentSum_projection hlim hfixed hsum hprojection

/--
[freePosSubcriticalMassBridge_of_capBound_boxRatioComponentShare_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_capBound_boxRatioComponentShare_projection_eq
  {capBound : BoundaryCrossingCapBound}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
  (hshare : BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical capBound)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_capBound_boxRatioComponentShare_projection hlim hfixed hcap hshare hprojection

/--
[freePosSubcriticalMassBridge_of_capBound_boxRatioComponentSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_capBound_boxRatioComponentSum_projection_eq
  {capBound : BoundaryCrossingCapBound}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
  (hcapNonneg : BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
  (hsum : BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical capBound)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_capBound_boxRatioComponentSum_projection hlim hfixed hcap hcapNonneg hsum hprojection

/--
[freePosSubcriticalMassBridge_of_boxRatioComponentThirds_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_boxRatioComponentThirds_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
  (hboundary : BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
  (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_boxRatioComponentThirds_projection hlim hfixed hone hboundary hempty hprojection

/--
[freePosSubcriticalMassBridge_of_capBound_boxRatioComponents_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_capBound_boxRatioComponents_projection_eq
  {capBound : BoundaryCrossingCapBound}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
  (hone : BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical capBound)
  (hboundary : BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical capBound)
  (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_capBound_boxRatioComponents_projection hlim hfixed hcap hone hboundary hempty hprojection

/--
[freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hshare : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection hlim hfixed hshare hprojection

/--
[freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hsum : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection hlim hfixed hsum hprojection

/--
[freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hshare : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection hlim hfixed hshare hprojection

/--
[freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hshare : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoff_projection hlim hfixed hshare hprojection

/--
[freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoff_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff_projection_eq
  {capBudget : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical capBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoff_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
  (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection hlim hfixed hone hboundary hempty hprojection

/--
[freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponents_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponents_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
  (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_sourceSectorMultiplicitySquareBoxRatioComponents_projection hlim hfixed hone hboundary hempty hprojection

/--
[freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponents_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponents_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hmajor : BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
  (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponents_projection hlim hfixed hmajor hone hboundary hempty hprojection

/--
[freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hmajor : BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
  (hshare : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentShare_projection hlim hfixed hmajor hshare hprojection

/--
[freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hmajor : BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
  (hsum : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSum_projection hlim hfixed hmajor hsum hprojection

/--
[freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hmajor : BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
  (h : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombined_projection hlim hfixed hmajor h hprojection

/--
[freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hmajor : BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
  (hshare : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoff_projection hlim hfixed hmajor hshare hprojection

/--
[freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hmajor : BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
  (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_decrementedSourceProfileMajorization_sourceSectorMultiplicitySquareBoxRatioUncutoffComponents_projection hlim hfixed hmajor hone hboundary hempty hprojection

/--
[freePosSubcriticalMassBridge_of_residualThresholdShellBudget15CanonicalRatioShareSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualThresholdShellBudget15CanonicalRatioShareSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualThresholdShellBudget15CanonicalRatioShareSum_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictCanonicalRatioShareSum_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_residualThresholdShellBudget15ComponentDenominatorFreeSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualThresholdShellBudget15ComponentDenominatorFreeSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualThresholdShellBudget15ComponentDenominatorFreeSum_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShare_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShare_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShare_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareSchedule_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareSchedule_projection_eq
  {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare : ResidualThresholdShellBudget15AggregateShareSchedule}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorptionPositiveSubcritical oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareSchedule_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareScheduleComponents_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareScheduleComponents_projection_eq
  {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare : ResidualThresholdShellBudget15AggregateShareSchedule}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hbudget : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBudgetPositiveSubcritical oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
  (hone : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePointPositiveSubcritical oneShare)
  (hboundary : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPairPositiveSubcritical boundaryPairShare)
  (hempty : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundaryPositiveSubcritical emptyBoundaryShare)
  (hshell : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudgetPositiveSubcritical shellBudgetShare)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualThresholdShellBudget15AggregateComponentShareScheduleComponents_projection hlim hfixed hbudget hone hboundary hempty hshell hprojection

/--
[freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainder_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainder_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainder_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderStrict_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderStrict_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderStrict_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSum_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hstrict : BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
  (hshare : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSum_projection hlim hfixed hstrict hshare hprojection

/--
[freePosSubcriticalMassBridge_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFree_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleComponents_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleComponents_projection_eq
  {budget : LiveSingletonOptionComponentBudgetSchedule}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hremaining : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical budget)
  (htail : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical budget)
  (hsingleton : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleSingletonPositiveSubcritical budget)
  (hpayment : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical budget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleComponents_projection hlim hfixed hremaining htail hsingleton hpayment hprojection

/--
[freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingleton_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingleton_projection_eq
  {budget : LiveSingletonOptionComponentBudgetSchedule}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hremaining : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical budget)
  (htail : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical budget)
  (hpayment : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical budget)
  (hsingletonResidual : LiveSingletonOptionComponentBudgetScheduleResidualCaseShareBudgetPositiveSubcritical budget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingleton_projection hlim hfixed hremaining htail hpayment hsingletonResidual hprojection

/--
[freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSign_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSign_projection_eq
  {schedule : LiveSingletonOptionShareSchedule}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical schedule)
  (hstrict : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical schedule)
  (hremaining : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical schedule)
  (htail : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical schedule)
  (hsingletonResidual : LiveSingletonOptionShareScheduleResidualCaseSingletonPayment schedule)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSign_projection hlim hfixed hR hstrict hremaining htail hsingletonResidual hprojection

/--
[freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSign_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSign_projection_eq
  {schedule : LiveSingletonOptionShareSchedule}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical schedule)
  (hstrict : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical schedule)
  (hremaining : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical schedule)
  (htail : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical schedule)
  (hsingletonResidual : LiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativePayment schedule)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSign_projection hlim hfixed hR hstrict hremaining htail hsingletonResidual hprojection

/--
[freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPayment_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPayment_projection_eq
  {schedule : LiveSingletonOptionShareSchedule}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical schedule)
  (hstrict : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical schedule)
  (hremaining : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical schedule)
  (htail : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical schedule)
  (hpayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment schedule)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPayment_projection hlim hfixed hR hstrict hremaining htail hpayment hprojection

/--
[freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPayment_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPayment_projection_eq
  {schedule : LiveSingletonOptionShareSchedule}
  {ι : {n : ℕ} → Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
  [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
  [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
  {label : ∀ {n : ℕ}, (Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) → (v : FK.boxVerts 3 n) → (x : Option (FK.boxVerts 3 n)) → finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι Ω v x}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical schedule)
  (hstrict : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical schedule)
  (hremaining : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical schedule)
  (htail : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical schedule)
  (hpayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment label schedule)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPayment_projection hlim hfixed hR hstrict hremaining htail hpayment hprojection

/--
[freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hraw : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotal_projection hlim hfixed hR hraw hprojection

/--
[freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositive_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositive_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hpos : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
  (hraw : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositive_projection hlim hfixed hpos hraw hprojection

/--
[freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hpaid : BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
  (hraw : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection hlim hfixed hpaid hraw hprojection

/--
[freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotal_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotal_projection_eq
  {ι : {n : ℕ} → Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
  [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
  [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
  {label : ∀ {n : ℕ}, (Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) → (v : FK.boxVerts 3 n) → (x : Option (FK.boxVerts 3 n)) → finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι Ω v x}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical label))
  (hraw : LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotal_projection hlim hfixed hR hraw hprojection

/--
[freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositive_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositive_projection_eq
  {ι : {n : ℕ} → Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
  [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
  [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
  {label : ∀ {n : ℕ}, (Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) → (v : FK.boxVerts 3 n) → (x : Option (FK.boxVerts 3 n)) → finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι Ω v x}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hpos : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
  (hraw : LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositive_projection hlim hfixed hpos hraw hprojection

/--
[freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection_eq
  {ι : {n : ℕ} → Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
  [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
  [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
  {label : ∀ {n : ℕ}, (Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) → (v : FK.boxVerts 3 n) → (x : Option (FK.boxVerts 3 n)) → finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι Ω v x}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hpaid : BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
  (hraw : LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSum_projection hlim hfixed hpaid hraw hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentSum_projection_eq
  {ι : (n : ℕ) → FK.boxVerts 3 n → Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → Type*}
  [∀ n v hasGhost hasOrigin hasEndpoint R, Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
  [∀ n v hasGhost hasOrigin hasEndpoint R, DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
  {label : ∀ {n : ℕ}, Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → (v : FK.boxVerts 3 n) → ∀ hasGhost hasOrigin hasEndpoint R, finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι n v hasGhost hasOrigin hasEndpoint R}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentSumAbsorptionPositiveSubcritical ι label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentSum_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentMajorantSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentMajorantSum_projection_eq
  {ι : (n : ℕ) → FK.boxVerts 3 n → Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → Type*}
  [∀ n v hasGhost hasOrigin hasEndpoint R, Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
  [∀ n v hasGhost hasOrigin hasEndpoint R, DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
  {label : ∀ {n : ℕ}, Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → (v : FK.boxVerts 3 n) → ∀ hasGhost hasOrigin hasEndpoint R, finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι n v hasGhost hasOrigin hasEndpoint R}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentMajorantSumAbsorptionPositiveSubcritical ι label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentMajorantSum_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum_projection_eq
  {ι : (n : ℕ) → FK.boxVerts 3 n → Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → Type*}
  [∀ n v hasGhost hasOrigin hasEndpoint R, Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
  [∀ n v hasGhost hasOrigin hasEndpoint R, DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
  {label : ∀ {n : ℕ}, Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → (v : FK.boxVerts 3 n) → ∀ hasGhost hasOrigin hasEndpoint R, finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι n v hasGhost hasOrigin hasEndpoint R}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical ι label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSum_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSum_projection_eq
  {ι : (n : ℕ) → FK.boxVerts 3 n → Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → Type*}
  [∀ n v hasGhost hasOrigin hasEndpoint R, Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
  [∀ n v hasGhost hasOrigin hasEndpoint R, DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
  {label : ∀ {n : ℕ}, Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → (v : FK.boxVerts 3 n) → ∀ hasGhost hasOrigin hasEndpoint R, finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι n v hasGhost hasOrigin hasEndpoint R}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSumAbsorptionPositiveSubcritical ι label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15ComponentDenominatorFreeMajorantSum_projection hlim hfixed h hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeRemainderPositive_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeRemainderPositive_projection_eq
  {ι : (n : ℕ) → FK.boxVerts 3 n → Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → Type*}
  [∀ n v hasGhost hasOrigin hasEndpoint R, Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
  [∀ n v hasGhost hasOrigin hasEndpoint R, DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
  {label : ∀ {n : ℕ}, Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → (v : FK.boxVerts 3 n) → ∀ hasGhost hasOrigin hasEndpoint R, finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι n v hasGhost hasOrigin hasEndpoint R}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hpos : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
  (hraw : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical ι label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeRemainderPositive_projection hlim hfixed hpos hraw hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictSum_projection_eq
  {ι : (n : ℕ) → FK.boxVerts 3 n → Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → Type*}
  [∀ n v hasGhost hasOrigin hasEndpoint R, Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
  [∀ n v hasGhost hasOrigin hasEndpoint R, DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
  {label : ∀ {n : ℕ}, Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → (v : FK.boxVerts 3 n) → ∀ hasGhost hasOrigin hasEndpoint R, finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι n v hasGhost hasOrigin hasEndpoint R}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hstrict : BoundaryCrossingCapComponentStrictSumPositiveSubcritical)
  (hraw : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical ι label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictSum_projection hlim hfixed hstrict hraw hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictShare_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictShare_projection_eq
  {ι : (n : ℕ) → FK.boxVerts 3 n → Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → Type*}
  [∀ n v hasGhost hasOrigin hasEndpoint R, Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
  [∀ n v hasGhost hasOrigin hasEndpoint R, DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
  {label : ∀ {n : ℕ}, Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → (v : FK.boxVerts 3 n) → ∀ hasGhost hasOrigin hasEndpoint R, finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι n v hasGhost hasOrigin hasEndpoint R}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hstrict : BoundaryCrossingCapComponentStrictSharePositiveSubcritical)
  (hraw : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical ι label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictShare_projection hlim hfixed hstrict hraw hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictCanonicalRatioShareSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictCanonicalRatioShareSum_projection_eq
  {ι : (n : ℕ) → FK.boxVerts 3 n → Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → Type*}
  [∀ n v hasGhost hasOrigin hasEndpoint R, Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
  [∀ n v hasGhost hasOrigin hasEndpoint R, DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
  {label : ∀ {n : ℕ}, Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → (v : FK.boxVerts 3 n) → ∀ hasGhost hasOrigin hasEndpoint R, finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι n v hasGhost hasOrigin hasEndpoint R}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hstrict : BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
  (hraw : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical ι label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawDenominatorFreeComponentStrictCanonicalRatioShareSum_projection hlim hfixed hstrict hraw hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawRemainderDenominatorFreeComponentStrictCanonicalRatioShareSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawRemainderDenominatorFreeComponentStrictCanonicalRatioShareSum_projection_eq
  {ι : (n : ℕ) → FK.boxVerts 3 n → Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → Type*}
  [∀ n v hasGhost hasOrigin hasEndpoint R, Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
  [∀ n v hasGhost hasOrigin hasEndpoint R, DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
  {label : ∀ {n : ℕ}, Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → (v : FK.boxVerts 3 n) → ∀ hasGhost hasOrigin hasEndpoint R, finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι n v hasGhost hasOrigin hasEndpoint R}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hstrict : BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
  (hraw : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderDenominatorFreeAbsorptionPositiveSubcritical ι label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderRawRemainderDenominatorFreeComponentStrictCanonicalRatioShareSum_projection hlim hfixed hstrict hraw hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderCanonicalRawRowRatioComponentStrictCanonicalRatioShareSum_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderCanonicalRawRowRatioComponentStrictCanonicalRatioShareSum_projection_eq
  {ι : (n : ℕ) → FK.boxVerts 3 n → Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → Type*}
  [∀ n v hasGhost hasOrigin hasEndpoint R, Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
  [∀ n v hasGhost hasOrigin hasEndpoint R, DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
  {label : ∀ {n : ℕ}, Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → (v : FK.boxVerts 3 n) → ∀ hasGhost hasOrigin hasEndpoint R, finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι n v hasGhost hasOrigin hasEndpoint R}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hstrict : BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
  (hrawRatio : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalRawRowDependentLabelBudget15CanonicalRatioShareSumPositiveSubcritical ι label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalRawRowDependentLabelBudget15BoundaryCrossingRemainderCanonicalRawRowRatioComponentStrictCanonicalRatioShareSum_projection hlim hfixed hstrict hrawRatio hprojection

/--
[freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hprofile : BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_profileSlack_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hprofile hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePayment_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePayment_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePayment_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hR hrawStrict hrawPayment hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_paidPlusProfileDominatesSimonPlusActive_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_paidPlusProfileDominatesSimonPlusActive_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hdom : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalPaidPlusProfileDominatesSimonPlusActiveWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_paidPlusProfileDominatesSimonPlusActive_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hdom hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_unpaidRemainderLeProfileSlack_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_unpaidRemainderLeProfileSlack_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hslack : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeProfileSlackWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_unpaidRemainderLeProfileSlack_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hslack hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_unpaidRemainderPlusActiveLeProfile_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_unpaidRemainderPlusActiveLeProfile_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hprofile : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusActiveLeProfileWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_unpaidRemainderPlusActiveLeProfile_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hprofile hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_unpaidRemainderPlusCollapsedActiveImageLeProfile_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_unpaidRemainderPlusCollapsedActiveImageLeProfile_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hcollapsed : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedActiveImageLeProfileWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_unpaidRemainderPlusCollapsedActiveImageLeProfile_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hcollapsed hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_targetMultiplicityMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_targetMultiplicityMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (htarget : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedTargetMultiplicityMainEmptyWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_targetMultiplicityMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict htarget hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_targetMultiplicityMainEmptySlackSplit_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_targetMultiplicityMainEmptySlackSplit_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hsplit : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderCollapsedTargetMultiplicityMainEmptySlackSplitWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_targetMultiplicityMainEmptySlackSplit_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hsplit hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_boundaryMultiplicityAndImageWeightLeMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_boundaryMultiplicityAndImageWeightLeMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hslack : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityAndImageWeightLeMainEmptyWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_boundaryMultiplicityAndImageWeightLeMainEmpty_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hslack hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmain : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderPlusCollapsedBoundaryMultiplicityMainAndCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hmain hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hempty : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalCollapsedBoundaryMultiplicityMainAndUnpaidRemainderPlusCollapsedImageWeightEmptyWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_boundaryMultiplicityMainAndUnpaidRemainderPlusImageWeightEmpty_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hempty hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixed_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixed_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmixed : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixed_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedDeficitNonpositive_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedDeficitNonpositive_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmixed : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedDeficitNonpositiveWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedDeficitNonpositive_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedPaymentDominates_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedPaymentDominates_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmixed : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedPaymentDominatesWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_reservoirSplitFallbackMixedPaymentDominates_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection

/--
[freeQ2BoundaryProfileSimonFreeSum_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmixed : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison hrawStrict hmixed hone hboundary hcmp

/--
[freePosSubcriticalMassBridge_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmixed : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedExpandedDemandWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_expandedDemand_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection

/--
[freeQ2BoundaryProfileSimonFreeSum_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmixed : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteAtomChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison hrawStrict hmixed hone hboundary hcmp

/--
[freePosSubcriticalMassBridge_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmixed : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteAtomChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_finiteAtomCharge_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection

/--
[freeQ2BoundaryProfileSimonFreeSum_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmixed : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteInjectionChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison hrawStrict hmixed hone hboundary hcmp

/--
[freePosSubcriticalMassBridge_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmixed : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteInjectionChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_finiteInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection

/--
[freeQ2BoundaryProfileSimonFreeSum_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmixed : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison hrawStrict hmixed hone hboundary hcmp

/--
[freePosSubcriticalMassBridge_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmixed : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedFiniteSetInjectionChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_finiteSetInjectionCharge_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hmixed hone hboundary hcmp hprojection

/--
[freeQ2BoundaryProfileSimonFreeSum_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hthreshold : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison hrawStrict hthreshold hone hboundary hcmp

/--
[freeQ2BoundaryProfileSimonFreeSum_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hranked : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison hrawStrict hranked hone hboundary hcmp

/--
[freeQ2BoundaryProfileSimonFreeSum_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hsorted : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison hrawStrict hsorted hone hboundary hcmp

/--
[freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hinjection : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison hrawStrict hinjection hone hboundary hcmp

/--
[freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hhall : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison hrawStrict hhall hone hboundary hcmp

/--
[freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hcapacityHall : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison hrawStrict hcapacityHall hone hboundary hcmp

/--
[freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hthreshold : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison hrawStrict hthreshold hone hboundary hcmp

/--
[freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hdisjoint : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison hrawStrict hdisjoint hone hboundary hcmp

/--
[freeQ2BoundaryProfileSimonFreeSum_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hthreshold : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison hrawStrict hthreshold hone hboundary hcmp

/--
[freeQ2BoundaryProfileSimonFreeSum_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hthreshold : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison hrawStrict hthreshold hone hboundary hcmp

/--
[freeQ2BoundaryProfileSimonFreeSum_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freeQ2BoundaryProfileSimonFreeSum_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison_eq
-- given
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hthreshold : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget) :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.freeQ2BoundaryProfileSimonFreeSum_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison hrawStrict hthreshold hone hboundary hcmp

/--
[freePosSubcriticalMassBridge_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hthreshold : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdScalarChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_scalarThreshold_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hranked : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityRankedPrefixChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_rankedPrefix_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hranked hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hsorted : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacitySortedAtomSlotChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_sortedAtomSlot_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hsorted hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hinjection : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotInjectionChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalSlotInjection_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hinjection hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalSlotSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalSlotSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hsubtypeInjection : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotSubtypeInjectionChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalSlotSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hsubtypeInjection hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_mainEmptyGapAllocation_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_mainEmptyGapAllocation_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hallocation : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapAllocationWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_mainEmptyGapAllocation_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hallocation hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_mainEmptyGap_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_mainEmptyGap_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hgap : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_mainEmptyGap_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hgap hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_mainEmptyGapMassSplit_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_mainEmptyGapMassSplit_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmass : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainEmptyGapMassSplitWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_mainEmptyGapMassSplit_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hmass hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_unpaidRemainderNonpositive_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_unpaidRemainderNonpositive_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hnonpos : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderNonpositiveWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_unpaidRemainderNonpositive_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hnonpos hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_mainGapSum_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_mainGapSum_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hmainGap : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedMainGapSumWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_mainGapSum_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hmainGap hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_emptyGap_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_emptyGap_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hemptyGap : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderLeCollapsedEmptyGapWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_emptyGap_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hemptyGap hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_reservoirBranchCover_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_reservoirBranchCover_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hbranch : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCoverWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_reservoirBranchCover_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_reservoirBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_reservoirBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hbranch : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchDisjunctionWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_reservoirBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_reservoirBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_reservoirBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection_eq
  {chooseBranch : UnpaidRemainderReservoirBranchSelector}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hbranch : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchSelectorWeightNonzeroPositiveSubcritical chooseBranch)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_reservoirBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_reservoirSplitBranchCover_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_reservoirSplitBranchCover_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hbranch : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchCoverWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_reservoirSplitBranchCover_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_reservoirSplitBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_reservoirSplitBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hbranch : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchDisjunctionWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_reservoirSplitBranchDisjunction_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_reservoirSplitBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_reservoirSplitBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection_eq
  {chooseBranch : UnpaidRemainderReservoirSplitBranchSelector}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hbranch : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical chooseBranch)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_reservoirSplitBranchSelector_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_reservoirSplitBranchFirstTrueSelector_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_reservoirSplitBranchFirstTrueSelector_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hbranch : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitBranchSelectorWeightNonzeroPositiveSubcritical unpaidRemainderReservoirSplitBranchFirstTrueSelector)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_reservoirSplitBranchFirstTrueSelector_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hbranch hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hhall : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotHallChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalSlotHall_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hhall hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hcapacityHall : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityHallChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalSlotCapacityHall_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hcapacityHall hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hthreshold : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalSlotCapacityThreshold_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hdisjoint : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_canonicalSlotCapacityDisjoint_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hdisjoint hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hthreshold : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdInjectionChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_thresholdInjection_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hthreshold : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdSubtypeInjectionChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_thresholdSubtypeInjection_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection

/--
[freePosSubcriticalMassBridge_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma freePosSubcriticalMassBridge_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison_projection_eq
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hthreshold : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityThresholdCandidateEmbeddingChargeWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical) :
-- imply
  FreePositiveSubcriticalMassBridge := by
-- proof
  apply StatMech.Exact3D.freePosSubcriticalMassBridge_of_thresholdCandidateEmbedding_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hrawStrict hthreshold hone hboundary hcmp hprojection

/--
[boundaryGhostComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma boundaryGhostComparison_eq
  {I : FiniteCurrentActualScheduleProjectionInputs} :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.boundaryGhostComparison I

/--
[simonFreeSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma simonFreeSum_eq
  {I : FiniteCurrentActualScheduleProjectionInputs} :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.simonFreeSum I

/--
[boundaryGhostComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma boundaryGhostComparison_eq_2
  {I : FiniteCurrentThresholdCandidateEmbeddingProjectionInputs} :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentThresholdCandidateEmbeddingProjectionInputs.boundaryGhostComparison I

/--
[simonFreeSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma simonFreeSum_eq_2
  {I : FiniteCurrentThresholdCandidateEmbeddingProjectionInputs} :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentThresholdCandidateEmbeddingProjectionInputs.simonFreeSum I

/--
[profileSlack](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma profileSlack_eq
  {I : FiniteCurrentExpandedDemandProjectionInputs} :
-- imply
  BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentExpandedDemandProjectionInputs.profileSlack I

/--
[boundaryGhostComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma boundaryGhostComparison_eq_3
  {I : FiniteCurrentExpandedDemandProjectionInputs} :
-- imply
  FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentExpandedDemandProjectionInputs.boundaryGhostComparison I

/--
[simonFreeSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma simonFreeSum_eq_3
  {I : FiniteCurrentExpandedDemandProjectionInputs} :
-- imply
  FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentExpandedDemandProjectionInputs.simonFreeSum I

/--
[ising3D_positiveMagnetizationSet_nonempty_of_meanfield](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_positiveMagnetizationSet_nonempty_of_meanfield_eq
-- given
  (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β) :
-- imply
  (Ising.positiveMagnetizationSet 3).Nonempty := by
-- proof
  apply StatMech.Exact3D.ising3D_positiveMagnetizationSet_nonempty_of_meanfield htc_pos hsqrt

/--
[ising3D_positiveMagnetizationSet_bddBelow_of_vanish_below_tildeBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_positiveMagnetizationSet_bddBelow_of_vanish_below_tildeBetaC_eq
-- given
  (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0) :
-- imply
  BddBelow (Ising.positiveMagnetizationSet 3) := by
-- proof
  apply StatMech.Exact3D.ising3D_positiveMagnetizationSet_bddBelow_of_vanish_below_tildeBetaC hzero

/--
[ising3D_tildeBetaCIsing_pos_of_positive_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_tildeBetaCIsing_pos_of_positive_mem_eq
  {β0 : ℝ}
-- given
  (hbdd : BddAbove (Sharpness.tildeBetaCIsingSet 3))
  (hβ0 : 0 < β0)
  (hmem : β0 ∈ Sharpness.tildeBetaCIsingSet 3) :
-- imply
  0 < Sharpness.tildeBetaCIsing 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_tildeBetaCIsing_pos_of_positive_mem hbdd hβ0 hmem

/--
[ising3D_tildeBetaCIsing_pos_of_positive_phi_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_tildeBetaCIsing_pos_of_positive_phi_witness_eq
  {β0 : ℝ}
  {S : Finset (StatMech.Lattice.Site 3)}
-- given
  (hbdd : BddAbove (Sharpness.tildeBetaCIsingSet 3))
  (hβ0 : 0 < β0)
  (hS : StatMech.Percolation.origin 3 ∈ S)
  (hphi : Sharpness.phiIsing 3 β0 S < 1) :
-- imply
  0 < Sharpness.tildeBetaCIsing 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_tildeBetaCIsing_pos_of_positive_phi_witness hbdd hβ0 S hS hphi

/--
[corrOriginInner_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma corrOriginInner_le_one_eq
  {d : ℕ}
  {β : ℝ}
  {S : Finset (StatMech.Lattice.Site d)}
  {x : StatMech.Lattice.Site d} :
-- imply
  Sharpness.corrOriginInner d β S x ≤ 1 := by
-- proof
  apply StatMech.Exact3D.corrOriginInner_le_one d β S x

/--
[phiIsing_le_tanh_mul_boundaryEdges_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma phiIsing_le_tanh_mul_boundaryEdges_card_eq
  {d : ℕ}
  {β : ℝ}
  {S : Finset (StatMech.Lattice.Site d)}
-- given
  (hβ : 0 ≤ β) :
-- imply
  Sharpness.phiIsing d β S ≤ Real.tanh β * (StatMech.Percolation.boundaryEdges d S).card := by
-- proof
  apply StatMech.Exact3D.phiIsing_le_tanh_mul_boundaryEdges_card d hβ S

/--
[phiIsing_le_tanh_mul_card_mul_two_d](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma phiIsing_le_tanh_mul_card_mul_two_d_eq
  {d : ℕ}
  {β : ℝ}
  {S : Finset (StatMech.Lattice.Site d)}
-- given
  (hβ : 0 ≤ β) :
-- imply
  Sharpness.phiIsing d β S ≤ Real.tanh β * (S.card * (2 * d)) := by
-- proof
  apply StatMech.Exact3D.phiIsing_le_tanh_mul_card_mul_two_d d hβ S

/--
[tildeBetaCIsingSet_mem_of_tanh_card_mul_two_d_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma tildeBetaCIsingSet_mem_of_tanh_card_mul_two_d_lt_one_eq
  {β : ℝ}
  {S : Finset (StatMech.Lattice.Site 3)}
-- given
  (hβ : 0 ≤ β)
  (hS : StatMech.Percolation.origin 3 ∈ S)
  (hsmall : Real.tanh β * (S.card * (2 * 3)) < 1) :
-- imply
  β ∈ Sharpness.tildeBetaCIsingSet 3 := by
-- proof
  apply StatMech.Exact3D.tildeBetaCIsingSet_mem_of_tanh_card_mul_two_d_lt_one hβ S hS hsmall

/--
[ising3D_tildeBetaCIsingSet_positive_singleton_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_tildeBetaCIsingSet_positive_singleton_mem_eq :
-- imply
  ising3DPositiveWitnessBeta ∈ Sharpness.tildeBetaCIsingSet 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_tildeBetaCIsingSet_positive_singleton_mem

/--
[ising3D_tildeBetaCIsing_pos_of_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_tildeBetaCIsing_pos_of_bddAbove_eq
-- given
  (hbdd : BddAbove (Sharpness.tildeBetaCIsingSet 3)) :
-- imply
  0 < Sharpness.tildeBetaCIsing 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_tildeBetaCIsing_pos_of_bddAbove hbdd

/--
[tildeBetaCIsingSet_bddAbove_of_phi_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma tildeBetaCIsingSet_bddAbove_of_phi_barrier_eq
  {B : ℝ}
-- given
  (hbarrier : ∀ β, B < β → ∀ S : Finset (StatMech.Lattice.Site 3), StatMech.Percolation.origin 3 ∈ S → 1 ≤ Sharpness.phiIsing 3 β S) :
-- imply
  BddAbove (Sharpness.tildeBetaCIsingSet 3) := by
-- proof
  apply StatMech.Exact3D.tildeBetaCIsingSet_bddAbove_of_phi_barrier hbarrier

/--
[ising3D_tildeBetaCIsing_pos_of_phi_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_tildeBetaCIsing_pos_of_phi_barrier_eq
  {B : ℝ}
-- given
  (hbarrier : ∀ β, B < β → ∀ S : Finset (StatMech.Lattice.Site 3), StatMech.Percolation.origin 3 ∈ S → 1 ≤ Sharpness.phiIsing 3 β S) :
-- imply
  0 < Sharpness.tildeBetaCIsing 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_tildeBetaCIsing_pos_of_phi_barrier hbarrier

/--
[tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_eventual_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_eventual_pos_eq
-- given
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (heventual : ∃ B : ℝ, ∀ β, B < β → 0 < Ising.magnetization 3 β) :
-- imply
  BddAbove (Sharpness.tildeBetaCIsingSet 3) := by
-- proof
  apply StatMech.Exact3D.tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_eventual_pos hzeroSet heventual

/--
[ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_eventual_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_eventual_pos_eq
-- given
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (heventual : ∃ B : ℝ, ∀ β, B < β → 0 < Ising.magnetization 3 β) :
-- imply
  0 < Sharpness.tildeBetaCIsing 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_eventual_pos hzeroSet heventual

/--
[transitionRegime](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma transitionRegime_eq
  {I : Ising3DTransitionAssemblyInputs} :
-- imply
  Ising3DTransitionRegime := by
-- proof
  apply StatMech.Exact3D.Ising3DTransitionAssemblyInputs.transitionRegime I

/--
[ising3D_transitionRegime_of_transitionAssemblyInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_transitionRegime_of_transitionAssemblyInputs_eq
  {I : Ising3DTransitionAssemblyInputs} :
-- imply
  Ising3DTransitionRegime := by
-- proof
  apply StatMech.Exact3D.ising3D_transitionRegime_of_transitionAssemblyInputs I

/--
[ising3D_eventual_positiveMagnetization_of_transition_regime](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_eventual_positiveMagnetization_of_transition_regime_eq
-- given
  (hregime : Ising3DTransitionRegime) :
-- imply
  ∃ B : ℝ, ∀ β, B < β → 0 < Ising.magnetization 3 β := by
-- proof
  apply StatMech.Exact3D.ising3D_eventual_positiveMagnetization_of_transition_regime hregime

/--
[tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_transition_regime](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_transition_regime_eq
-- given
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (hregime : Ising3DTransitionRegime) :
-- imply
  BddAbove (Sharpness.tildeBetaCIsingSet 3) := by
-- proof
  apply StatMech.Exact3D.tildeBetaCIsingSet_bddAbove_of_zero_on_set_and_transition_regime hzeroSet hregime

/--
[ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_transition_regime](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_transition_regime_eq
-- given
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (hregime : Ising3DTransitionRegime) :
-- imply
  0 < Sharpness.tildeBetaCIsing 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_tildeBetaCIsing_pos_of_zero_on_set_and_transition_regime hzeroSet hregime

/--
[exists_tildeBetaCIsingSet_member_gt_of_lt_tildeBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma exists_tildeBetaCIsingSet_member_gt_of_lt_tildeBetaC_eq
  {β : ℝ}
-- given
  (hβ : β < Sharpness.tildeBetaCIsing 3) :
-- imply
  ∃ γ ∈ Sharpness.tildeBetaCIsingSet 3, β < γ := by
-- proof
  apply StatMech.Exact3D.exists_tildeBetaCIsingSet_member_gt_of_lt_tildeBetaC hβ

/--
[ising3D_magnetization_monotone_of_volume_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_magnetization_monotone_of_volume_tendsto_eq
  {volumeMag : ℕ → ℝ → ℝ}
-- given
  (hfiniteMono : ∀ N, Monotone (volumeMag N))
  (hfullLimit : ∀ β, Filter.Tendsto (fun N : ℕ => volumeMag N β) Filter.atTop (nhds (Ising.magnetization 3 β))) :
-- imply
  Monotone (Ising.magnetization 3) := by
-- proof
  apply StatMech.Exact3D.ising3D_magnetization_monotone_of_volume_tendsto hfiniteMono hfullLimit

/--
[ising3D_vanish_below_tildeBetaC_of_zero_on_set_monotone_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_vanish_below_tildeBetaC_of_zero_on_set_monotone_nonneg_eq
-- given
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (hmono : Monotone (Ising.magnetization 3))
  (hnonneg : ∀ β, 0 ≤ Ising.magnetization 3 β) :
-- imply
  ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0 := by
-- proof
  apply StatMech.Exact3D.ising3D_vanish_below_tildeBetaC_of_zero_on_set_monotone_nonneg hzeroSet hmono hnonneg

/--
[ising3D_vanish_below_tildeBetaC_of_zero_on_set_volumeMonotone_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_vanish_below_tildeBetaC_of_zero_on_set_volumeMonotone_nonneg_eq
  {volumeMag : ℕ → ℝ → ℝ}
-- given
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (hfiniteMono : ∀ N, Monotone (volumeMag N))
  (hfullLimit : ∀ β, Filter.Tendsto (fun N : ℕ => volumeMag N β) Filter.atTop (nhds (Ising.magnetization 3 β)))
  (hnonneg : ∀ β, 0 ≤ Ising.magnetization 3 β) :
-- imply
  ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0 := by
-- proof
  apply StatMech.Exact3D.ising3D_vanish_below_tildeBetaC_of_zero_on_set_volumeMonotone_nonneg hzeroSet hfiniteMono hfullLimit hnonneg

/--
[ising3D_not_positive_below_tildeBetaC_of_zero_on_set_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_not_positive_below_tildeBetaC_of_zero_on_set_monotone_eq
-- given
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (hmono : Monotone (Ising.magnetization 3)) :
-- imply
  ∀ β, β < Sharpness.tildeBetaCIsing 3 → ¬ 0 < Ising.magnetization 3 β := by
-- proof
  apply StatMech.Exact3D.ising3D_not_positive_below_tildeBetaC_of_zero_on_set_monotone hzeroSet hmono

/--
[ising3D_not_positive_below_tildeBetaC_of_zero_on_set_volumeMonotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_not_positive_below_tildeBetaC_of_zero_on_set_volumeMonotone_eq
  {volumeMag : ℕ → ℝ → ℝ}
-- given
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (hfiniteMono : ∀ N, Monotone (volumeMag N))
  (hfullLimit : ∀ β, Filter.Tendsto (fun N : ℕ => volumeMag N β) Filter.atTop (nhds (Ising.magnetization 3 β))) :
-- imply
  ∀ β, β < Sharpness.tildeBetaCIsing 3 → ¬ 0 < Ising.magnetization 3 β := by
-- proof
  apply StatMech.Exact3D.ising3D_not_positive_below_tildeBetaC_of_zero_on_set_volumeMonotone hzeroSet hfiniteMono hfullLimit

/--
[ising3D_betaC_pos_of_sharpness_bc_eq_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_pos_of_sharpness_bc_eq_inputs_eq
-- given
  (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
  (hbdd : BddBelow (Ising.positiveMagnetizationSet 3))
  (hne : (Ising.positiveMagnetizationSet 3).Nonempty)
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0) :
-- imply
  0 < Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_pos_of_sharpness_bc_eq_inputs htc_pos hbdd hne hsqrt hzero

/--
[ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_hne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_hne_eq
-- given
  (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
  (hbdd : BddBelow (Ising.positiveMagnetizationSet 3))
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0) :
-- imply
  0 < Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_hne htc_pos hbdd hsqrt hzero

/--
[ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions_eq
-- given
  (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0) :
-- imply
  0 < Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions htc_pos hsqrt hzero

/--
[ising3D_betaC_pos_of_sharpness_bc_eq_inputs_tilde_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_pos_of_sharpness_bc_eq_inputs_tilde_bddAbove_eq
-- given
  (hbddTilde : BddAbove (Sharpness.tildeBetaCIsingSet 3))
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0) :
-- imply
  0 < Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_pos_of_sharpness_bc_eq_inputs_tilde_bddAbove hbddTilde hsqrt hzero

/--
[ising3D_betaC_pos_of_sharpness_bc_eq_inputs_phi_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_pos_of_sharpness_bc_eq_inputs_phi_barrier_eq
  {B : ℝ}
-- given
  (hbarrier : ∀ β, B < β → ∀ S : Finset (StatMech.Lattice.Site 3), StatMech.Percolation.origin 3 ∈ S → 1 ≤ Sharpness.phiIsing 3 β S)
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0) :
-- imply
  0 < Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_pos_of_sharpness_bc_eq_inputs_phi_barrier hbarrier hsqrt hzero

/--
[ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos_eq
-- given
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (heventual : ∃ B : ℝ, ∀ β, B < β → 0 < Ising.magnetization 3 β)
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0) :
-- imply
  0 < Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos hzeroSet heventual hsqrt hzero

/--
[ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos_monotone_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos_monotone_nonneg_eq
-- given
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (heventual : ∃ B : ℝ, ∀ β, B < β → 0 < Ising.magnetization 3 β)
  (hmono : Monotone (Ising.magnetization 3))
  (hnonneg : ∀ β, 0 ≤ Ising.magnetization 3 β)
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β) :
-- imply
  0 < Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos_monotone_nonneg hzeroSet heventual hmono hnonneg hsqrt

/--
[ising3D_betaC_pos_of_tilde_pos_meanfield_not_positive_below](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_pos_of_tilde_pos_meanfield_not_positive_below_eq
-- given
  (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hnotpos : ∀ β, β < Sharpness.tildeBetaCIsing 3 → ¬ 0 < Ising.magnetization 3 β) :
-- imply
  0 < Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_pos_of_tilde_pos_meanfield_not_positive_below htc_pos hsqrt hnotpos

/--
[ising3D_betaC_pos_of_sharpness_zeroSet_eventual_pos_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_pos_of_sharpness_zeroSet_eventual_pos_monotone_eq
-- given
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (heventual : ∃ B : ℝ, ∀ β, B < β → 0 < Ising.magnetization 3 β)
  (hmono : Monotone (Ising.magnetization 3))
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β) :
-- imply
  0 < Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_pos_of_sharpness_zeroSet_eventual_pos_monotone hzeroSet heventual hmono hsqrt

/--
[ising3D_betaC_pos_of_sharpness_zeroSet_transition_regime_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_pos_of_sharpness_zeroSet_transition_regime_monotone_eq
-- given
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (hregime : Ising3DTransitionRegime)
  (hmono : Monotone (Ising.magnetization 3))
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β) :
-- imply
  0 < Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_pos_of_sharpness_zeroSet_transition_regime_monotone hzeroSet hregime hmono hsqrt

/--
[ising3D_betaC_pos_of_sharpness_zeroSet_transitionAssembly_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_pos_of_sharpness_zeroSet_transitionAssembly_monotone_eq
-- given
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hmono : Monotone (Ising.magnetization 3))
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β) :
-- imply
  0 < Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_pos_of_sharpness_zeroSet_transitionAssembly_monotone hzeroSet htransition hmono hsqrt

/--
[ising3D_betaC_pos_of_transition_regime_nonpositive_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_pos_of_transition_regime_nonpositive_beta_eq
-- given
  (hregime : Ising3DTransitionRegime)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
-- imply
  0 < Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_pos_of_transition_regime_nonpositive_beta hregime hnonpos

/--
[ising3D_exists_betaC_eq_transition_threshold_of_transition_regime_nonpositive_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_exists_betaC_eq_transition_threshold_of_transition_regime_nonpositive_beta_eq
-- given
  (hregime : Ising3DTransitionRegime)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
-- imply
  ∃ β0 : ℝ, 0 < β0 ∧ Ising.betaC 3 = β0 ∧ (∀ β, 0 < β → β < β0 → Ising.magnetization 3 β = 0) ∧ (∀ β, β0 < β → 0 < Ising.magnetization 3 β) := by
-- proof
  apply StatMech.Exact3D.ising3D_exists_betaC_eq_transition_threshold_of_transition_regime_nonpositive_beta hregime hnonpos

/--
[ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transition_regime](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transition_regime_eq
-- given
  (hregime : Ising3DTransitionRegime) :
-- imply
  ∃ β0 : ℝ, 0 < β0 ∧ IsingFK.betaC (Ising.magnetization 3) = β0 ∧ (∀ β, 0 < β → β < β0 → Ising.magnetization 3 β = 0) ∧ (∀ β, β0 < β → 0 < Ising.magnetization 3 β) := by
-- proof
  apply StatMech.Exact3D.ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transition_regime hregime

/--
[ising3D_betaC_eq_IsingFK_betaC_of_transition_regime_nonpositive_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_eq_IsingFK_betaC_of_transition_regime_nonpositive_beta_eq
-- given
  (hregime : Ising3DTransitionRegime)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
-- imply
  Ising.betaC 3 = IsingFK.betaC (Ising.magnetization 3) := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_eq_IsingFK_betaC_of_transition_regime_nonpositive_beta hregime hnonpos

/--
[ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transitionAssembly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transitionAssembly_eq
-- given
  (htransition : Ising3DTransitionAssemblyInputs) :
-- imply
  ∃ β0 : ℝ, 0 < β0 ∧ IsingFK.betaC (Ising.magnetization 3) = β0 ∧ (∀ β, 0 < β → β < β0 → Ising.magnetization 3 β = 0) ∧ (∀ β, β0 < β → 0 < Ising.magnetization 3 β) := by
-- proof
  apply StatMech.Exact3D.ising3D_exists_IsingFK_betaC_eq_transition_threshold_of_transitionAssembly htransition

/--
[ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta_eq
-- given
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
-- imply
  Ising.betaC 3 = IsingFK.betaC (Ising.magnetization 3) := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta htransition hnonpos

/--
[ising3D_exists_betaC_eq_transition_threshold_of_transitionAssembly_nonpositive_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_exists_betaC_eq_transition_threshold_of_transitionAssembly_nonpositive_beta_eq
-- given
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
-- imply
  ∃ β0 : ℝ, 0 < β0 ∧ Ising.betaC 3 = β0 ∧ (∀ β, 0 < β → β < β0 → Ising.magnetization 3 β = 0) ∧ (∀ β, β0 < β → 0 < Ising.magnetization 3 β) := by
-- proof
  apply StatMech.Exact3D.ising3D_exists_betaC_eq_transition_threshold_of_transitionAssembly_nonpositive_beta htransition hnonpos

/--
[ising3D_betaC_pos_of_transitionAssembly_nonpositive_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_betaC_pos_of_transitionAssembly_nonpositive_beta_eq
-- given
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta) :
-- imply
  0 < Ising.betaC 3 := by
-- proof
  apply StatMech.Exact3D.ising3D_betaC_pos_of_transitionAssembly_nonpositive_beta htransition hnonpos

/--
[rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hmass : FreePositiveSubcriticalMassBridge)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
  (hexact : FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C hselected.fkMass) :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw C hagree hmass hβeq hβc hselected hexact

/--
[hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hmass : FreePositiveSubcriticalMassBridge)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
  (hexact : FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw C hagree hmass hβeq hβc hselected hexact

/--
[rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogAffine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogAffine_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hmass : FreePositiveSubcriticalMassBridge)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
  (hlog : FreePositiveSubcriticalMassFKPCLogAffineNearCritical C hselected.fkMass) :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogAffine C hagree hmass hβeq hβc hselected hlog

/--
[hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogAffine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogAffine_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hmass : FreePositiveSubcriticalMassBridge)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
  (hlog : FreePositiveSubcriticalMassFKPCLogAffineNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogAffine C hagree hmass hβeq hβc hselected hlog

/--
[rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hmass : FreePositiveSubcriticalMassBridge)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
  (hratio : FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C hselected.fkMass) :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit C hagree hmass hβeq hβc hselected hratio

/--
[hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hmass : FreePositiveSubcriticalMassBridge)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
  (hratio : FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit C hagree hmass hβeq hβc hselected hratio

/--
[rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hmass : FreePositiveSubcriticalMassBridge)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
  (hsand : FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C hselected.fkMass) :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich C hagree hmass hβeq hβc hselected hsand

/--
[hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hmass : FreePositiveSubcriticalMassBridge)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
  (hsand : FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich C hagree hmass hβeq hβc hselected hsand

/--
[rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hmass : FreePositiveSubcriticalMassBridge)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hisingLength : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), T.isingCorrelationLength β = freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β) :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq C hagree hmass hβeq hβc T hisingLength

/--
[hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hmass : FreePositiveSubcriticalMassBridge)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hisingLength : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), T.isingCorrelationLength β = freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq C hagree hmass hβeq hβc T hisingLength

/--
[rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hmass : FreePositiveSubcriticalMassBridge)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hisingLength : T.isingCorrelationLength = freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass) :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq C hagree hmass hβeq hβc T hisingLength

/--
[hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hmass : FreePositiveSubcriticalMassBridge)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hisingLength : T.isingCorrelationLength = freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq C hagree hmass hβeq hβc T hisingLength

/--
[ising3D_liminfCorrelationLength_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu I C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_asymptoticPowerLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_asymptoticPowerLaw_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hasymp : FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_asymptoticPowerLaw I C hagree hasymp

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_logAffine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_logAffine_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlog : FreePositiveSubcriticalMassLogAffineNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_logAffine I C hagree hlog

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hratio : FreePositiveSubcriticalMassLogRatioLimitNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit I C hagree hratio

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioSandwich_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hsand : FreePositiveSubcriticalMassLogRatioSandwichNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioSandwich I C hagree hsand

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_powerSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_powerSandwich_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpow : FreePositiveSubcriticalMassPowerSandwichNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_powerSandwich I C hagree hpow

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerUpper_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical C I.massBridge)
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerUpper I C hagree hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooExistsLowerUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooExistsLowerUpper_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical C I.massBridge)
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooExistsLowerUpper I C hagree hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsUpperExists_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical C I.massBridge)
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsUpperExists I C hagree hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C I.massBridge)
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists I C hagree hβc hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCLowerBoundExistsNoWindowUpperExists_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hlower : FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C I.massBridge)
  (hupper : FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCLowerBoundExistsNoWindowUpperExists I C hagree hβeq hβc hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCIooSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCIooSandwich_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hsand : FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCIooSandwich I C hagree hβeq hβc hsand

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCIooSandwich_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCIooSandwich_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hsand : FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical D I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCIooSandwich_congr_predictedExponent I C D hpred hagree hβeq hβc hsand

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCPullbackIooSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCPullbackIooSandwich_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hpull : FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCPullbackIooSandwich I C hagree hβeq hβc hpull

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCPullbackIooSandwich_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCPullbackIooSandwich_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hpull : FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical D I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCPullbackIooSandwich_congr_predictedExponent I C D hpred hagree hβeq hβc hpull

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCCanonicalWindowPullbackIooSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCCanonicalWindowPullbackIooSandwich_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hcanon : FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCCanonicalWindowPullbackIooSandwich I C hagree hβeq hβc hcanon

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCCanonicalWindowPullbackIooSandwich_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCCanonicalWindowPullbackIooSandwich_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hcanon : FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical D I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCCanonicalWindowPullbackIooSandwich_congr_predictedExponent I C D hpred hagree hβeq hβc hcanon

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedIooSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedIooSandwich_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hp : FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedIooSandwich I C hagree hβeq hβc hp

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedIooSandwich_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedIooSandwich_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hp : FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical D I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedIooSandwich_congr_predictedExponent I C D hpred hagree hβeq hβc hp

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpper_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hlower : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical C hselected.fkMass)
  (hupper : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpper I C hagree hβeq hβc hselected hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExists_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hlower : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical C hselected.fkMass)
  (hupper : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExists I C hagree hβeq hβc hselected hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpper_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpper_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hlower : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical D hselected.fkMass)
  (hupper : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical D hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpper_congr_predictedExponent I C D hpred hagree hβeq hβc hselected hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExists_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExists_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hlower : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical D hselected.fkMass)
  (hupper : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical D hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExists_congr_predictedExponent I C D hpred hagree hβeq hβc hselected hlower hupper

/--
[hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementExactPowerLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementExactPowerLaw_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hexact : FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementExactPowerLaw I C hagree hβeq hβc hselected hexact

/--
[hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogAffine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogAffine_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hlog : FreePositiveSubcriticalMassFKPCLogAffineNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogAffine I C hagree hβeq hβc hselected hlog

/--
[hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hratio : FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit I C hagree hβeq hβc hselected hratio

/--
[hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioSandwich_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hsand : FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioSandwich I C hagree hβeq hβc hselected hsand

/--
[hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetEventuallyLengthEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetEventuallyLengthEq_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hisingLength : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), T.isingCorrelationLength β = freeSelectedPositiveSubcriticalCorrelationLengthFromMass I.massBridge β) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetEventuallyLengthEq I C hagree hβeq hβc T hisingLength

/--
[hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetLengthEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetLengthEq_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hisingLength : T.isingCorrelationLength = freeSelectedPositiveSubcriticalCorrelationLengthFromMass I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetLengthEq I C hagree hβeq hβc T hisingLength

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumDoubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumDoubledBoxPolynomialProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumDoubledBoxPolynomialProjection hlim hdecay hfinite hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumDoubledBoxPolynomialProjection hlim hdecay hfinite hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonDoubledBoxPolynomialProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonDoubledBoxPolynomialProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonDoubledBoxPolynomialProjection hlim hdecay hSimon hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonDoubledBoxPolynomialProjection hlim hdecay hSimon hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeCoordinateStepBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeCoordinateStepBranches_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeCoordinateStepBranches hlim hdecay hfinite hstrict hdiag).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeCoordinateStepBranches hlim hdecay hfinite hstrict hdiag C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeCoordinateStepBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeCoordinateStepBranches_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeCoordinateStepBranches hlim hdecay hSimon hstrict hdiag).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeCoordinateStepBranches hlim hdecay hSimon hstrict hdiag C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale hlim hdecay hfinite hstrict hdiag hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale hlim hdecay hfinite hstrict hdiag hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrict : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
  (hdiag : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale hlim hdecay hSimon hstrict hdiag hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale hlim hdecay hSimon hstrict hdiag hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hone : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale hlim hdecay hfinite hone hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale hlim hdecay hfinite hone hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hone : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale hlim hdecay hSimon hone hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale hlim hdecay hSimon hone hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (honeLocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale hlim hdecay hfinite honeLocal hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale hlim hdecay hfinite honeLocal hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (honeLocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale hlim hdecay hSimon honeLocal hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale hlim hdecay hSimon honeLocal hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYCoordinateComparisonLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictZ : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hstrictY : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfiniteAt : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in Filter.atTop, FreeQ2BoundaryProfileFiniteFKSimonFreeSumAt β hβpos n)
  (honeLocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
  (hprofileAt : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in Filter.atTop, FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt hlim hdecay hfiniteAt honeLocal hprofileAt).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt hlim hdecay hfiniteAt honeLocal hprofileAt C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimonAt : ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in Filter.atTop, FiniteQ2SimonFreeBoundaryIsingBoxAt β n)
  (honeLocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
  (hprofileAt : ∀ β (hβpos : 0 < β), β < Ising.betaC 3 → ∀ᶠ n in Filter.atTop, FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt hlim hdecay hSimonAt honeLocal hprofileAt).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt hlim hdecay hSimonAt honeLocal hprofileAt C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfinite : FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
  (hstrictLocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagLocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale hlim hdecay hfinite hstrictLocal hdiagLocal hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale hlim hdecay hfinite hstrictLocal hdiagLocal hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hSimon : FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
  (hstrictLocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
  (hdiagLocal : FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
  (hprofile : FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale hlim hdecay hSimon hstrictLocal hdiagLocal hprofile).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale hlim hdecay hSimon hstrictLocal hdiagLocal hprofile C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2ExactRestrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2ExactRestrictedCylinderComparison_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2ExactPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFreeFVQ2ExactRestrictedCylinderComparison hcmp hdecay).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2ExactRestrictedCylinderComparison hcmp hdecay C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2SubexpRestrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2SubexpRestrictedCylinderComparison_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2SubexpPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFreeFVQ2SubexpRestrictedCylinderComparison hcmp hdecay).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2SubexpRestrictedCylinderComparison hcmp hdecay C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedRestrictedCylinderComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedRestrictedCylinderComparison_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFreeFVQ2TwoSidedRestrictedCylinderComparison hcmp hdecay).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedRestrictedCylinderComparison hcmp hdecay C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_boundaryGhostComparisonProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_boundaryGhostComparisonProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hcomparison : FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofBoundaryGhostComparisonProjection hlim hfixed hcomparison hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_boundaryGhostComparisonProjection hlim hfixed hcomparison hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_boundaryGhostFirstExitPositiveProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_boundaryGhostFirstExitPositiveProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hfirst : FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofBoundaryGhostFirstExitPositiveProjection hlim hdecay hfirst hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_boundaryGhostFirstExitPositiveProjection hlim hdecay hfirst hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_boxGeometryComponentThirdsAbsorptionProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_boxGeometryComponentThirdsAbsorptionProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hthirds : BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofBoxGeometryComponentThirdsAbsorptionProjection hlim hdecay hthirds hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_boxGeometryComponentThirdsAbsorptionProjection hlim hdecay hthirds hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentShareProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentShareProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofBoxRatioComponentShareProjection hlim hdecay hshare hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentShareProjection hlim hdecay hshare hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentSumProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentSumProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofBoxRatioComponentSumProjection hlim hdecay hsum hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentSumProjection hlim hdecay hsum hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentShareProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentShareProjection_eq
  {capBound : BoundaryCrossingCapBound}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
  (hshare : BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical capBound)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofCapBoundBoxRatioComponentShareProjection hlim hdecay hcap hshare hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentShareProjection hlim hdecay hcap hshare hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentSumProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentSumProjection_eq
  {capBound : BoundaryCrossingCapBound}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
  (hcapNonneg : BoundaryCrossingCapBoundNonnegativePositiveSubcritical capBound)
  (hsum : BoundaryCrossingCapBoxRatioComponentSumWithBoundPositiveSubcritical capBound)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofCapBoundBoxRatioComponentSumProjection hlim hdecay hcap hcapNonneg hsum hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentSumProjection hlim hdecay hcap hcapNonneg hsum hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentThirdsProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentThirdsProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
  (hboundary : BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
  (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofBoxRatioComponentThirdsProjection hlim hdecay hone hboundary hempty hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentThirdsProjection hlim hdecay hone hboundary hempty hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentsProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentsProjection_eq
  {capBound : BoundaryCrossingCapBound}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
  (hone : BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdWithBoundPositiveSubcritical capBound)
  (hboundary : BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdWithBoundPositiveSubcritical capBound)
  (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofCapBoundBoxRatioComponentsProjection hlim hdecay hcap hone hboundary hempty hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentsProjection hlim hdecay hcap hone hboundary hempty hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentShareProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentShareProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hshare : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofSourceSectorMultiplicitySquareBoxRatioComponentShareProjection hlim hdecay hshare hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentShareProjection hlim hdecay hshare hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentSumProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentSumProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hsum : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofSourceSectorMultiplicitySquareBoxRatioComponentSumProjection hlim hdecay hsum hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentSumProjection hlim hdecay hsum hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (h : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection hlim hdecay h hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection hlim hdecay h hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hshare : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection hlim hdecay hshare hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection hlim hdecay hshare hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hshare : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffProjection hlim hdecay hshare hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffProjection hlim hdecay hshare hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (h : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffProjection hlim hdecay h hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffProjection hlim hdecay h hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffProjection_eq
  {capBudget : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (h : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical capBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffProjection hlim hdecay h hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffProjection hlim hdecay h hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
  (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection hlim hdecay hone hboundary hempty hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection hlim hdecay hone hboundary hempty hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentsProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentsProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
  (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofSourceSectorMultiplicitySquareBoxRatioComponentsProjection hlim hdecay hone hboundary hempty hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentsProjection hlim hdecay hone hboundary hempty hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentsProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentsProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hmajor : BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
  (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentsProjection hlim hdecay hmajor hone hboundary hempty hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentsProjection hlim hdecay hmajor hone hboundary hempty hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentShareProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentShareProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hmajor : BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
  (hshare : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentShareProjection hlim hdecay hmajor hshare hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentShareProjection hlim hdecay hmajor hshare hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hmajor : BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
  (hsum : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumProjection hlim hdecay hmajor hsum hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumProjection hlim hdecay hmajor hsum hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hmajor : BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
  (h : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection hlim hdecay hmajor h hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection hlim hdecay hmajor h hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hmajor : BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
  (hshare : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection hlim hdecay hmajor hshare hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection hlim hdecay hmajor hshare hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hmajor : BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
  (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection hlim hdecay hmajor hone hboundary hempty hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection hlim hdecay hmajor hone hboundary hempty hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15CanonicalRatioShareSumProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15CanonicalRatioShareSumProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualThresholdShellBudget15CanonicalRatioShareSumProjection hlim hdecay h hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15CanonicalRatioShareSumProjection hlim hdecay h hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15StrictCanonicalRatioShareSumProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15StrictCanonicalRatioShareSumProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualThresholdShellBudget15StrictCanonicalRatioShareSumProjection hlim hdecay h hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15StrictCanonicalRatioShareSumProjection hlim hdecay h hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15ComponentDenominatorFreeSumProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15ComponentDenominatorFreeSumProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualThresholdShellBudget15ComponentDenominatorFreeSumProjection hlim hdecay h hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15ComponentDenominatorFreeSumProjection hlim hdecay h hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualThresholdShellBudget15AggregateComponentShareProjection hlim hdecay h hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareProjection hlim hdecay h hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareScheduleProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareScheduleProjection_eq
  {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare : ResidualThresholdShellBudget15AggregateShareSchedule}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorptionPositiveSubcritical oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualThresholdShellBudget15AggregateComponentShareScheduleProjection hlim hdecay h hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareScheduleProjection hlim hdecay h hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareScheduleComponentsProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareScheduleComponentsProjection_eq
  {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare : ResidualThresholdShellBudget15AggregateShareSchedule}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hbudget : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBudgetPositiveSubcritical oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
  (hone : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePointPositiveSubcritical oneShare)
  (hboundary : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPairPositiveSubcritical boundaryPairShare)
  (hempty : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundaryPositiveSubcritical emptyBoundaryShare)
  (hshell : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudgetPositiveSubcritical shellBudgetShare)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualThresholdShellBudget15AggregateComponentShareScheduleComponentsProjection hlim hdecay hbudget hone hboundary hempty hshell hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareScheduleComponentsProjection hlim hdecay hbudget hone hboundary hempty hshell hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualThresholdShellBudget15BoundaryCrossingRemainderProjection hlim hdecay h hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderProjection hlim hdecay h hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderStrictProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderStrictProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualThresholdShellBudget15BoundaryCrossingRemainderStrictProjection hlim hdecay h hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderStrictProjection hlim hdecay h hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSumProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSumProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualThresholdShellBudget15StrictComponentDenominatorFreeSumProjection hlim hdecay h hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSumProjection hlim hdecay h hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSumProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSumProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hstrict : BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
  (hshare : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSumProjection hlim hdecay hstrict hshare hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSumProjection hlim hdecay hstrict hshare hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFreeProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFreeProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (h : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeProjection hlim hdecay h hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFreeProjection hlim hdecay h hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionComponentBudgetScheduleComponentsProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionComponentBudgetScheduleComponentsProjection_eq
  {budget : LiveSingletonOptionComponentBudgetSchedule}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hremaining : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical budget)
  (htail : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical budget)
  (hsingleton : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleSingletonPositiveSubcritical budget)
  (hpayment : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical budget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofLiveSingletonOptionComponentBudgetScheduleComponentsProjection hlim hdecay hremaining htail hsingleton hpayment hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionComponentBudgetScheduleComponentsProjection hlim hdecay hremaining htail hsingleton hpayment hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonProjection_eq
  {budget : LiveSingletonOptionComponentBudgetSchedule}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hremaining : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical budget)
  (htail : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical budget)
  (hpayment : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetSchedulePaymentPositiveSubcritical budget)
  (hsingletonResidual : LiveSingletonOptionComponentBudgetScheduleResidualCaseShareBudgetPositiveSubcritical budget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofLiveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonProjection hlim hdecay hremaining htail hpayment hsingletonResidual hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonProjection hlim hdecay hremaining htail hpayment hsingletonResidual hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignProjection_eq
  {schedule : LiveSingletonOptionShareSchedule}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical schedule)
  (hstrict : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical schedule)
  (hremaining : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical schedule)
  (htail : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical schedule)
  (hsingletonResidual : LiveSingletonOptionShareScheduleResidualCaseSingletonPayment schedule)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofLiveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignProjection hlim hdecay hR hstrict hremaining htail hsingletonResidual hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignProjection hlim hdecay hR hstrict hremaining htail hsingletonResidual hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSignProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSignProjection_eq
  {schedule : LiveSingletonOptionShareSchedule}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical schedule)
  (hstrict : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical schedule)
  (hremaining : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical schedule)
  (htail : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical schedule)
  (hsingletonResidual : LiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativePayment schedule)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofLiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSignProjection hlim hdecay hR hstrict hremaining htail hsingletonResidual hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSignProjection hlim hdecay hR hstrict hremaining htail hsingletonResidual hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPaymentProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPaymentProjection_eq
  {schedule : LiveSingletonOptionShareSchedule}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical schedule)
  (hstrict : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical schedule)
  (hremaining : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical schedule)
  (htail : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical schedule)
  (hpayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsPayment schedule)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPaymentProjection hlim hdecay hR hstrict hremaining htail hpayment hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPaymentProjection hlim hdecay hR hstrict hremaining htail hpayment hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPaymentProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPaymentProjection_eq
  {schedule : LiveSingletonOptionShareSchedule}
  {ι : {n : ℕ} → Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
  [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
  [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
  {label : ∀ {n : ℕ}, (Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) → (v : FK.boxVerts 3 n) → (x : Option (FK.boxVerts 3 n)) → finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι Ω v x}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical schedule)
  (hstrict : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical schedule)
  (hremaining : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainingPositiveSubcritical schedule)
  (htail : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailPositiveSubcritical schedule)
  (hpayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsPayment label schedule)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPaymentProjection hlim hdecay hR hstrict hremaining htail hpayment hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPaymentProjection hlim hdecay hR hstrict hremaining htail hpayment hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_logRatioLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_logRatioLimit_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hratio : FreePositiveSubcriticalMassLogRatioLimitNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_logRatioLimit hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection C hagree hratio

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_powerSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_powerSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpow : FreePositiveSubcriticalMassPowerSandwichNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_powerSandwich hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection C hagree hpow

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerUpper_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge)
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerUpper hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection C hagree hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooExistsLowerUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooExistsLowerUpper_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge)
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooExistsLowerUpper hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection C hagree hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerBoundExistsUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerBoundExistsUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge)
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerBoundExistsUpperExists hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection C hagree hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge)
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection C hagree hβc hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkBetaCIooSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkBetaCIooSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hsand : FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkBetaCIooSandwich hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection C hagree hβeq hβc hsand

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCPullbackIooSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCPullbackIooSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hpull : FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCPullbackIooSandwich hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection C hagree hβeq hβc hpull

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCCanonicalWindowPullbackIooSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCCanonicalWindowPullbackIooSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hcanon : FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCCanonicalWindowPullbackIooSandwich hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection C hagree hβeq hβc hcanon

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedIooSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedIooSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hp : FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedIooSandwich hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection C hagree hβeq hβc hp

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedAgreementLowerUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedAgreementLowerUpper_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge)
  (hlower : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical C hselected.fkMass)
  (hupper : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedAgreementLowerUpper hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection C hagree hβeq hβc hselected hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedAgreementLowerUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedAgreementLowerUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hrawStrict : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hrawPayment : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawProfilePaymentWeightNonzeroPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection).massBridge)
  (hlower : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical C hselected.fkMass)
  (hupper : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedAgreementLowerUpperExists hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection C hagree hβeq hβc hselected hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
  (hraw : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalProjection hlim hdecay hR hraw hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalProjection hlim hdecay hR hraw hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalProjection_eq
  {ι : {n : ℕ} → Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
  [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
  [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
  {label : ∀ {n : ℕ}, (Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) → (v : FK.boxVerts 3 n) → (x : Option (FK.boxVerts 3 n)) → finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι Ω v x}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hR : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical (liveSingletonOptionShareScheduleOfResidualCaseNormalizedLabelRowsCanonical label))
  (hraw : LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalProjection hlim hdecay hR hraw hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalProjection hlim hdecay hR hraw hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositiveProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositiveProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hpos : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
  (hraw : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositiveProjection hlim hdecay hpos hraw hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositiveProjection hlim hdecay hpos hraw hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hpaid : BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
  (hraw : LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection hlim hdecay hpaid hraw hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection hlim hdecay hpaid hraw hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositiveProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositiveProjection_eq
  {ι : {n : ℕ} → Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
  [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
  [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
  {label : ∀ {n : ℕ}, (Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) → (v : FK.boxVerts 3 n) → (x : Option (FK.boxVerts 3 n)) → finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι Ω v x}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hpos : BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
  (hraw : LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositiveProjection hlim hdecay hpos hraw hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositiveProjection hlim hdecay hpos hraw hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection_eq
  {ι : {n : ℕ} → Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) → FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
  [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
  [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
  {label : ∀ {n : ℕ}, (Ω : Finset (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) → (v : FK.boxVerts 3 n) → (x : Option (FK.boxVerts 3 n)) → finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι Ω v x}
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hpaid : BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
  (hraw : LiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalPositiveSubcritical label)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection hlim hdecay hpaid hraw hprojection).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection hlim hdecay hpaid hraw hprojection C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis hlim hdecay hcompare).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis hlim hdecay hcompare C hagree hpower

/--
[hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogAffine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogAffine_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis hlim hdecay hcompare).massBridge)
  (hlog : FreePositiveSubcriticalMassFKPCLogAffineNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogAffine hlim hdecay hcompare C hagree hβeq hβc hselected hlog

/--
[hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogRatioLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogRatioLimit_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis hlim hdecay hcompare).massBridge)
  (hratio : FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogRatioLimit hlim hdecay hcompare C hagree hβeq hβc hselected hratio

/--
[hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogRatioSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogRatioSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis hlim hdecay hcompare).massBridge)
  (hsand : FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogRatioSandwich hlim hdecay hcompare C hagree hβeq hβc hselected hsand

/--
[hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementExactPowerLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementExactPowerLaw_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis hlim hdecay hcompare).massBridge)
  (hexact : FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementExactPowerLaw hlim hdecay hcompare C hagree hβeq hβc hselected hexact

/--
[hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCFKMassPowerLawTargetEventuallyLengthEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCFKMassPowerLawTargetEventuallyLengthEq_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hisingLength : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), T.isingCorrelationLength β = freeSelectedPositiveSubcriticalCorrelationLengthFromMass (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis hlim hdecay hcompare).massBridge β) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCFKMassPowerLawTargetEventuallyLengthEq hlim hdecay hcompare C hagree hβeq hβc T hisingLength

/--
[hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCFKMassPowerLawTargetLengthEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCFKMassPowerLawTargetLengthEq_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (hcompare : FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hisingLength : T.isingCorrelationLength = freeSelectedPositiveSubcriticalCorrelationLengthFromMass (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis hlim hdecay hcompare).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCFKMassPowerLawTargetLengthEq hlim hdecay hcompare C hagree hβeq hβc T hisingLength

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper hlim hdecay htension).massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper hlim hdecay htension C hagree hpower

/--
[hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper_fkPCSelectedAgreementExactPowerLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper_fkPCSelectedAgreementExactPowerLaw_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper hlim hdecay htension).massBridge)
  (hexact : FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper_fkPCSelectedAgreementExactPowerLaw hlim hdecay htension C hagree hβeq hβc hselected hexact

/--
[hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper_fkPCFKMassPowerLawTargetEventuallyLengthEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper_fkPCFKMassPowerLawTargetEventuallyLengthEq_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
  (htension : FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hisingLength : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), T.isingCorrelationLength β = freeSelectedPositiveSubcriticalCorrelationLengthFromMass (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper hlim hdecay htension).massBridge β) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentMassBridgeInputs.hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper_fkPCFKMassPowerLawTargetEventuallyLengthEq hlim hdecay htension C hagree hβeq hβc T hisingLength

/--
[ising3D_liminfCorrelationLength_hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu I C hagree hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_asymptoticPowerLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_asymptoticPowerLaw_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hasymp : FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_asymptoticPowerLaw I C hagree hasymp

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_logAffine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_logAffine_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlog : FreePositiveSubcriticalMassLogAffineNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_logAffine I C hagree hlog

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hratio : FreePositiveSubcriticalMassLogRatioLimitNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit I C hagree hratio

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_analyticLogRatioBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_analyticLogRatioBridge_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hbridge : AnalyticLogRatioBridge I C) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_analyticLogRatioBridge I C hbridge

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioSandwich_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hsand : FreePositiveSubcriticalMassLogRatioSandwichNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioSandwich I C hagree hsand

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_powerSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_powerSandwich_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hpow : FreePositiveSubcriticalMassPowerSandwichNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_powerSandwich I C hagree hpow

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_subpowerPrefactorSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_subpowerPrefactorSandwich_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hsub : FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_subpowerPrefactorSandwich I C hagree hsub

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_boundedPrefactorSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_boundedPrefactorSandwich_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hbounded : FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_boundedPrefactorSandwich I C hagree hbounded

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakSandwich_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hconst : FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakSandwich I C hagree hconst

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooSandwich_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hIoo : FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooSandwich I C hagree hIoo

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerUpper_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical C I.massBridge)
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerUpper I C hagree hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooExistsLowerUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooExistsLowerUpper_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical C I.massBridge)
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooExistsLowerUpper I C hagree hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsUpperExists_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical C I.massBridge)
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsUpperExists I C hagree hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists_eq_2
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C I.massBridge)
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists I C hagree hβc hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_eq
  {C : RGCertificate Ising3DModel}
  {δ : ℝ}
  {massPrefactor : ℝ → ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hδ : 0 < δ)
  (hδle : δ ≤ Ising.betaC 3)
  (hmassPrefactor_pos : ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) → 0 < massPrefactor β)
  (hmassPrefactor_log_negligible : Filter.Tendsto (fun β : ℝ => Real.log (massPrefactor β) / Real.log (Ising.betaC 3 - β)) (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
  (hmass_scaling : ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) → freeSelectedPositiveSubcriticalMass (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection) β = massPrefactor β * Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection C hagree hlim hfixed hone hboundary hcmp hprojection δ hδ hδle massPrefactor hmassPrefactor_pos hmassPrefactor_log_negligible hmass_scaling

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_powerLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_powerLaw_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hpower : FreePositiveSubcriticalMassExactPowerLawNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_powerLaw C hagree hlim hfixed hone hboundary hcmp hprojection hpower

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_asymptoticPowerLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_asymptoticPowerLaw_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hasymp : FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_asymptoticPowerLaw C hagree hlim hfixed hone hboundary hcmp hprojection hasymp

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logAffine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logAffine_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hlog : FreePositiveSubcriticalMassLogAffineNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logAffine C hagree hlim hfixed hone hboundary hcmp hprojection hlog

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logRatioLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logRatioLimit_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hratio : FreePositiveSubcriticalMassLogRatioLimitNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logRatioLimit C hagree hlim hfixed hone hboundary hcmp hprojection hratio

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logRatioSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logRatioSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hsand : FreePositiveSubcriticalMassLogRatioSandwichNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logRatioSandwich C hagree hlim hfixed hone hboundary hcmp hprojection hsand

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_powerSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_powerSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hpow : FreePositiveSubcriticalMassPowerSandwichNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_powerSandwich C hagree hlim hfixed hone hboundary hcmp hprojection hpow

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_subpowerPrefactorSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_subpowerPrefactorSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hsub : FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_subpowerPrefactorSandwich C hagree hlim hfixed hone hboundary hcmp hprojection hsub

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_boundedPrefactorSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_boundedPrefactorSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hbounded : FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_boundedPrefactorSandwich C hagree hlim hfixed hone hboundary hcmp hprojection hbounded

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hconst : FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakSandwich C hagree hlim hfixed hone hboundary hcmp hprojection hconst

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooSandwich_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hIoo : FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooSandwich C hagree hlim hfixed hone hboundary hcmp hprojection hIoo

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerUpper_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerUpper C hagree hlim hfixed hone hboundary hcmp hprojection hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooExistsLowerUpper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooExistsLowerUpper_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooExistsLowerUpper C hagree hlim hfixed hone hboundary hcmp hprojection hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hβc : 0 < Ising.betaC 3)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection hβc hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_sharpnessLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_sharpnessLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
  (hbdd : BddBelow (Ising.positiveMagnetizationSet 3))
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_sharpnessLowerBoundExistsNoWindowUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection htc_pos hbdd hsqrt hzero hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_sharpnessNoSideLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_sharpnessNoSideLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_sharpnessNoSideLowerBoundExistsNoWindowUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection htc_pos hsqrt hzero hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_tildeWitnessSharpnessLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_tildeWitnessSharpnessLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
  {β0 : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hbddTilde : BddAbove (Sharpness.tildeBetaCIsingSet 3))
  (hβ0 : 0 < β0)
  (hβ0mem : β0 ∈ Sharpness.tildeBetaCIsingSet 3)
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_tildeWitnessSharpnessLowerBoundExistsNoWindowUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection hbddTilde hβ0 hβ0mem hsqrt hzero hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_tildeBddSharpnessLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_tildeBddSharpnessLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hbddTilde : BddAbove (Sharpness.tildeBetaCIsingSet 3))
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_tildeBddSharpnessLowerBoundExistsNoWindowUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection hbddTilde hsqrt hzero hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_phiBarrierSharpnessLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_phiBarrierSharpnessLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
  {B : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hbarrier : ∀ β, B < β → ∀ S : Finset (StatMech.Lattice.Site 3), StatMech.Percolation.origin 3 ∈ S → 1 ≤ Sharpness.phiIsing 3 β S)
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_phiBarrierSharpnessLowerBoundExistsNoWindowUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection hbarrier hsqrt hzero hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualSharpnessLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualSharpnessLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (heventual : ∃ B : ℝ, ∀ β, B < β → 0 < Ising.magnetization 3 β)
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 → Ising.magnetization 3 β = 0)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualSharpnessLowerBoundExistsNoWindowUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection hzeroSet heventual hsqrt hzero hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualMonotoneSharpnessLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualMonotoneSharpnessLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (heventual : ∃ B : ℝ, ∀ β, B < β → 0 < Ising.magnetization 3 β)
  (hmono : Monotone (Ising.magnetization 3))
  (hnonneg : ∀ β, 0 ≤ Ising.magnetization 3 β)
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualMonotoneSharpnessLowerBoundExistsNoWindowUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection hzeroSet heventual hmono hnonneg hsqrt hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (heventual : ∃ B : ℝ, ∀ β, B < β → 0 < Ising.magnetization 3 β)
  (hmono : Monotone (Ising.magnetization 3))
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection hzeroSet heventual hmono hsqrt hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetTransitionMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetTransitionMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (hregime : Ising3DTransitionRegime)
  (hmono : Monotone (Ising.magnetization 3))
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetTransitionMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection hzeroSet hregime hmono hsqrt hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetTransitionAssemblyMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetTransitionAssemblyMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 → Ising.magnetization 3 β = 0)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hmono : Monotone (Ising.magnetization 3))
  (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β → Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤ Ising.magnetization 3 β)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetTransitionAssemblyMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection hzeroSet htransition hmono hsqrt hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_transitionAssemblyNonpositiveBetaLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_transitionAssemblyNonpositiveBetaLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hlower : FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_transitionAssemblyNonpositiveBetaLowerBoundExistsNoWindowUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCTransitionAssemblyNonpositiveBetaLowerBoundExistsNoWindowUpperExists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCTransitionAssemblyNonpositiveBetaLowerBoundExistsNoWindowUpperExists_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hlower : FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hupper : FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCTransitionAssemblyNonpositiveBetaLowerBoundExistsNoWindowUpperExists C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCIooSandwichTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCIooSandwichTransitionAssemblyNonpositiveBeta_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hsand : FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCIooSandwichTransitionAssemblyNonpositiveBeta C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos hsand

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCPullbackIooSandwichTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCPullbackIooSandwichTransitionAssemblyNonpositiveBeta_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hpull : FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCPullbackIooSandwichTransitionAssemblyNonpositiveBeta C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos hpull

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCCanonicalWindowPullbackIooSandwichTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCCanonicalWindowPullbackIooSandwichTransitionAssemblyNonpositiveBeta_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hcanon : FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCCanonicalWindowPullbackIooSandwichTransitionAssemblyNonpositiveBeta C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos hcanon

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedIooSandwichTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedIooSandwichTransitionAssemblyNonpositiveBeta_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hp : FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical C (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedIooSandwichTransitionAssemblyNonpositiveBeta C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos hp

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperTransitionAssemblyNonpositiveBeta_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hlower : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical C hselected.fkMass)
  (hupper : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperTransitionAssemblyNonpositiveBeta C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos hselected hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperExistsTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperExistsTransitionAssemblyNonpositiveBeta_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hlower : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical C hselected.fkMass)
  (hupper : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperExistsTransitionAssemblyNonpositiveBeta C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos hselected hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hexact : FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos hselected hexact

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hratio : FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos hselected hratio

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta_eq
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hsand : FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos hselected hsand

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hfkMass : T.fkMass = hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos hselected T hfkMass

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEqTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEqTransitionAssemblyNonpositiveBeta_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection))
  (hfkMass : ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC), T.fkMass p = hselected.fkMass p) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEqTransitionAssemblyNonpositiveBeta C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos hselected T hfkMass

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetLengthEqTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetLengthEqTransitionAssemblyNonpositiveBeta_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hisingLength : T.isingCorrelationLength = freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetLengthEqTransitionAssemblyNonpositiveBeta C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos T hisingLength

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetEventuallyLengthEqTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetEventuallyLengthEqTransitionAssemblyNonpositiveBeta_eq
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
  (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
  (hone : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryOnePointActualSchedulePaymentPositiveSubcritical)
  (hboundary : BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioAggregateEnvelopeActualBoundaryBoundaryPairActualSchedulePaymentPositiveSubcritical)
  (hcmp : BoundaryCrossingCapBoxRatioEmptyBoundaryEmptyCollapsedSourcePairRatioComparisonPositiveSubcritical boundaryCrossingCapBoxRatioEmptyBoundaryAllowedSourcePairBudget)
  (hprojection : FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hisingLength : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), T.isingCorrelationLength β = freeSelectedPositiveSubcriticalCorrelationLengthFromMass (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection hlim hfixed hone hboundary hcmp hprojection) β) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetEventuallyLengthEqTransitionAssemblyNonpositiveBeta C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos T hisingLength

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperTransitionAssemblyNonpositiveBeta_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hlower : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical C hselected.fkMass)
  (hupper : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperTransitionAssemblyNonpositiveBeta I C hagree htransition hnonpos hselected hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExistsTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExistsTransitionAssemblyNonpositiveBeta_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hlower : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical C hselected.fkMass)
  (hupper : FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExistsTransitionAssemblyNonpositiveBeta I C hagree htransition hnonpos hselected hlower hupper

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hexact : FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta I C hagree htransition hnonpos hselected hexact

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogAffineTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogAffineTransitionAssemblyNonpositiveBeta_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hlog : FreePositiveSubcriticalMassFKPCLogAffineNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogAffineTransitionAssemblyNonpositiveBeta I C hagree htransition hnonpos hselected hlog

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hratio : FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta I C hagree htransition hnonpos hselected hratio

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hsand : FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta I C hagree htransition hnonpos hselected hsand

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hfkMass : T.fkMass = hselected.fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta I C hagree htransition hnonpos hselected T hfkMass

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEqTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEqTransitionAssemblyNonpositiveBeta_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge)
  (hfkMass : ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC), T.fkMass p = hselected.fkMass p) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEqTransitionAssemblyNonpositiveBeta I C hagree htransition hnonpos hselected T hfkMass

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCFKMassPowerLawTargetLengthEqTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCFKMassPowerLawTargetLengthEqTransitionAssemblyNonpositiveBeta_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hisingLength : T.isingCorrelationLength = freeSelectedPositiveSubcriticalCorrelationLengthFromMass I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCFKMassPowerLawTargetLengthEqTransitionAssemblyNonpositiveBeta I C hagree htransition hnonpos T hisingLength

/--
[ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCFKMassPowerLawTargetEventuallyLengthEqTransitionAssemblyNonpositiveBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean)
-/
@[path]
private lemma ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCFKMassPowerLawTargetEventuallyLengthEqTransitionAssemblyNonpositiveBeta_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
  {T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hisingLength : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), T.isingCorrelationLength β = freeSelectedPositiveSubcriticalCorrelationLengthFromMass I.massBridge β) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCFKMassPowerLawTargetEventuallyLengthEqTransitionAssemblyNonpositiveBeta I C hagree htransition hnonpos T hisingLength


-- created on 2026-10-23
