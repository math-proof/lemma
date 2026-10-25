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
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part23


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection
      C hagree hlim hfixed hone hboundary hcmp hprojection δ hδ hδle
      massPrefactor hmassPrefactor_pos hmassPrefactor_log_negligible
      hmass_scaling)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_powerLaw
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_powerLaw
      C hagree hlim hfixed hone hboundary hcmp hprojection hpower)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_asymptoticPowerLaw
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_asymptoticPowerLaw
      C hagree hlim hfixed hone hboundary hcmp hprojection hasymp)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logAffine
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_logAffine
      C hagree hlim hfixed hone hboundary hcmp hprojection hlog)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logRatioLimit
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_logRatioLimit
      C hagree hlim hfixed hone hboundary hcmp hprojection hratio)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_logRatioSandwich
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_logRatioSandwich
      C hagree hlim hfixed hone hboundary hcmp hprojection hsand)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_powerSandwich
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_powerSandwich
      C hagree hlim hfixed hone hboundary hcmp hprojection hpow)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_subpowerPrefactorSandwich
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_subpowerPrefactorSandwich
      C hagree hlim hfixed hone hboundary hcmp hprojection hsub)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_boundedPrefactorSandwich
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_boundedPrefactorSandwich
      C hagree hlim hfixed hone hboundary hcmp hprojection hbounded)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakSandwich
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakSandwich
      C hagree hlim hfixed hone hboundary hcmp hprojection hconst)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooSandwich
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooSandwich
      C hagree hlim hfixed hone hboundary hcmp hprojection hIoo)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerUpper
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerUpper
      C hagree hlim hfixed hone hboundary hcmp hprojection hlower hupper)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooExistsLowerUpper
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooExistsLowerUpper
      C hagree hlim hfixed hone hboundary hcmp hprojection hlower hupper)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsUpperExists
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsUpperExists
      C hagree hlim hfixed hone hboundary hcmp hprojection hlower hupper)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
      C hagree hlim hfixed hone hboundary hcmp hprojection hβc hlower hupper)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_sharpnessLowerBoundExistsNoWindowUpperExists
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
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hbdd : BddBelow (Ising.positiveMagnetizationSet 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_hne
      htc_pos hbdd hsqrt hzero)
    hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_sharpnessNoSideLowerBoundExistsNoWindowUpperExists
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
    (htc_pos : 0 < Sharpness.tildeBetaCIsing 3)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_bc_eq_inputs_no_side_conditions
      htc_pos hsqrt hzero)
    hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_tildeWitnessSharpnessLowerBoundExistsNoWindowUpperExists
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
    (hbddTilde : BddAbove (Sharpness.tildeBetaCIsingSet 3))
    {β0 : ℝ}
    (hβ0 : 0 < β0)
    (hβ0mem : β0 ∈ Sharpness.tildeBetaCIsingSet 3)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_sharpnessNoSideLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_tildeBetaCIsing_pos_of_positive_mem
      hbddTilde hβ0 hβ0mem)
    hsqrt hzero hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_tildeBddSharpnessLowerBoundExistsNoWindowUpperExists
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
    (hbddTilde : BddAbove (Sharpness.tildeBetaCIsingSet 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_bc_eq_inputs_tilde_bddAbove
      hbddTilde hsqrt hzero)
    hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_phiBarrierSharpnessLowerBoundExistsNoWindowUpperExists
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
    {B : ℝ}
    (hbarrier : ∀ β, B < β →
      ∀ S : Finset (StatMech.Lattice.Site 3),
        StatMech.Percolation.origin 3 ∈ S →
          1 ≤ Sharpness.phiIsing 3 β S)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_bc_eq_inputs_phi_barrier
      hbarrier hsqrt hzero)
    hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualSharpnessLowerBoundExistsNoWindowUpperExists
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
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hzero : ∀ β, β < Sharpness.tildeBetaCIsing 3 →
      Ising.magnetization 3 β = 0)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos
      hzeroSet heventual hsqrt hzero)
    hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualMonotoneSharpnessLowerBoundExistsNoWindowUpperExists
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
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β)
    (hmono : Monotone (Ising.magnetization 3))
    (hnonneg : ∀ β, 0 ≤ Ising.magnetization 3 β)
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_bc_eq_inputs_zeroSet_eventual_pos_monotone_nonneg
      hzeroSet heventual hmono hnonneg hsqrt)
    hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists
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
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (heventual : ∃ B : ℝ, ∀ β, B < β →
      0 < Ising.magnetization 3 β)
    (hmono : Monotone (Ising.magnetization 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_sharpness_zeroSet_eventual_pos_monotone
      hzeroSet heventual hmono hsqrt)
    hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetTransitionMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists
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
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (hregime : Ising3DTransitionRegime)
    (hmono : Monotone (Ising.magnetization 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetEventualMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection hzeroSet
    (ising3D_eventual_positiveMagnetization_of_transition_regime hregime)
    hmono hsqrt hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetTransitionAssemblyMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists
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
    (hzeroSet : ∀ β, β ∈ Sharpness.tildeBetaCIsingSet 3 →
      Ising.magnetization 3 β = 0)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hmono : Monotone (Ising.magnetization 3))
    (hsqrt : ∀ β, Sharpness.tildeBetaCIsing 3 ≤ β →
      Real.sqrt (1 - (Sharpness.tildeBetaCIsing 3 / β) ^ 2) ≤
        Ising.magnetization 3 β)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_zeroSetTransitionMonotoneDirectSharpnessLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection hzeroSet
    htransition.transitionRegime hmono hsqrt hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_transitionAssemblyNonpositiveBetaLowerBoundExistsNoWindowUpperExists
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hlim hfixed hone hboundary hcmp hprojection
    (ising3D_betaC_pos_of_transitionAssembly_nonpositive_beta
      htransition hnonpos)
    hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCTransitionAssemblyNonpositiveBetaLowerBoundExistsNoWindowUpperExists
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hlower :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hupper :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCLowerBoundExistsNoWindowUpperExists
      C hagree
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      (by
        simpa [Ising3DFKBetaC] using
          ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
            htransition hnonpos)
      (ising3D_betaC_pos_of_transitionAssembly_nonpositive_beta
        htransition hnonpos)
      hlower hupper)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCIooSandwichTransitionAssemblyNonpositiveBeta
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCIooSandwich
      C hagree
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      (by
        simpa [Ising3DFKBetaC] using
          ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
            htransition hnonpos)
      (ising3D_betaC_pos_of_transitionAssembly_nonpositive_beta
        htransition hnonpos)
      hsand)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCPullbackIooSandwichTransitionAssemblyNonpositiveBeta
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCIooSandwichTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    (freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCPullback
      C
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      hpull)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCCanonicalWindowPullbackIooSandwichTransitionAssemblyNonpositiveBeta
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCPullbackIooSandwichTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    (freePositiveSubcriticalMassFKPCPullback_of_canonicalWindowPullback
      C
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      hcanon)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedIooSandwichTransitionAssemblyNonpositiveBeta
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkBetaCIooSandwichTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    (freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCSelectedIooSandwich
      C
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      hp)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperTransitionAssemblyNonpositiveBeta
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical C
        hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedIooSandwichTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lower_upper
      C
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      hselected hlower hupper)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperExistsTransitionAssemblyNonpositiveBeta
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical C
        hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedIooSandwichTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lowerUpperExists
      C
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      hselected hlower hupper)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedIooSandwichTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_exactPowerLaw
      C
      (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
        hlim hfixed hone hboundary hcmp hprojection)
      hselected hexact)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioLimit
      C hselected.fkMass hratio)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    hselected
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
      C hselected.fkMass hsand)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass : T.fkMass = hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget_eq
      C
      (by
        simpa [Ising3DFKBetaC] using
          ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
            htransition hnonpos)
      T hfkMass)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEqTransitionAssemblyNonpositiveBeta
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection))
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        T.fkMass p = hselected.fkMass p) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget_eventuallyEq
      C
      (by
        simpa [Ising3DFKBetaC] using
          ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
            htransition hnonpos)
      T hfkMass)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetLengthEqTransitionAssemblyNonpositiveBeta
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
            hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hmass :=
    freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_lengthEq
      C hmass
      (by
        simpa [Ising3DFKBetaC] using
          ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
            htransition hnonpos)
      T hisingLength
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    hselected T rfl

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetEventuallyLengthEqTransitionAssemblyNonpositiveBeta
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
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass
            (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
              hlim hfixed hone hboundary hcmp hprojection) β) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hmass :=
    freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
      hlim hfixed hone hboundary hcmp hprojection
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_eventuallyLengthEq
      C hmass
      (by
        simpa [Ising3DFKBetaC] using
          ising3D_betaC_eq_IsingFK_betaC_of_transitionAssembly_nonpositive_beta
            htransition hnonpos)
      T hisingLength
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta
    C hagree hlim hfixed hone hboundary hcmp hprojection htransition hnonpos
    hselected T rfl

namespace FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExistsTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLowerUpperExistsTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected hexact

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogAffineTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementExactPowerLawTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_logAffineNearCritical
      C hselected.fkMass hlog)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected hratio

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C
        hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected hsand

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass : T.fkMass = hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected T hfkMass

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEqTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfkMass :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        T.fkMass p = hselected.fkMass p) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCSelectedAgreementFKMassPowerLawTargetEventuallyEqTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos
    hselected T hfkMass

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCFKMassPowerLawTargetLengthEqTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetLengthEqTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos T
    hisingLength

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCFKMassPowerLawTargetEventuallyLengthEqTransitionAssemblyNonpositiveBeta
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass
            I.massBridge β) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_fkPCFKMassPowerLawTargetEventuallyLengthEqTransitionAssemblyNonpositiveBeta
    C hagree I.thermodynamicLimit I.fixedInner I.onePointPayment
    I.boundaryPairPayment I.emptyComparison I.projection htransition hnonpos T
    hisingLength

end FiniteCurrentActualScheduleProjectionInputs
end Exact3D
end StatMech
