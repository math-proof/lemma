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
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part15


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalMass
            (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
              hlim hfixed hone hboundary hcmp hprojection) β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    δ hδ hδle massPrefactor hmassPrefactor_pos
    hmassPrefactor_log_negligible hmass_scaling

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_powerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hpower

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassAsymptoticPowerLaw
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hasymp

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_logAffine
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogAffineNearCritical
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hlog

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_logRatioLimit
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioLimit
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hratio

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioSandwich
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hsand

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_powerSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassPowerSandwich
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hpow

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_subpowerPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassSubpowerPrefactorSandwich
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hsub

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_boundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassBoundedPrefactorSandwich
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hbounded

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakSandwich
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hconst

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooSandwich
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hIoo

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerUpper
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooExistsLowerUpper
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooExistsLowerUpper
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsUpperExists
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hlower hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree
    (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection)
    hβc hlower hupper

end Exact3D
end StatMech
