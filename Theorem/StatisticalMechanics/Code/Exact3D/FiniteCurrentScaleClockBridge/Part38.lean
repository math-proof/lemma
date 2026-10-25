/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part47


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_from_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalError
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
    (hterm :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalErrorNearCritical C
        (freePosSubcriticalMassBridge_of_actualSchedulePayments_allowedEmptyComparison_projection
          hlim hfixed hone hboundary hcmp hprojection)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (freeMassPowerLawToPlusTarget_of_actualSchedulePayments_allowedEmptyComparison_projection_annulusScaleClockTerminalError
      C hagree hlim hfixed hone hboundary hcmp hprojection hterm)

end Exact3D
end StatMech
