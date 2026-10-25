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
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part22


namespace StatMech

namespace Exact3D

namespace FiniteCurrentActualScheduleProjectionInputs

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_logRatioLimit C hagree hratio)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_analyticLogRatioBridge
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hbridge : AnalyticLogRatioBridge I C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  I.ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit
    C hbridge.plus_free_agree hbridge.free_mass_log_ratio

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_logRatioSandwich C hagree hsand)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_powerSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_powerSandwich C hagree hpow)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_subpowerPrefactorSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_subpowerPrefactorSandwich
      C hagree hsub)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_boundedPrefactorSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_boundedPrefactorSandwich
      C hagree hbounded)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakSandwich
      C hagree hconst)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooSandwich
      C hagree hIoo)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerUpper
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerUpper
      C hagree hlower hupper)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooExistsLowerUpper
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooExistsLowerUpper
      C hagree hlower hupper)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsUpperExists
      C hagree hlower hupper)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C I.massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
      C hagree hβc hlower hupper)

end FiniteCurrentActualScheduleProjectionInputs
end Exact3D
end StatMech
