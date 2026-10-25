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
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part20


namespace StatMech

namespace Exact3D

namespace FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget C hagree hpower)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_asymptoticPowerLaw
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_asymptoticPowerLaw C hagree hasymp)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_logAffine
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C (I.freeMassPowerLawToPlusTarget_of_logAffine C hagree hlog)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit
    (I : FiniteCurrentMassBridgeInputs)
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


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioSandwich
    (I : FiniteCurrentMassBridgeInputs)
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
    (I : FiniteCurrentMassBridgeInputs)
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


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerUpper
    (I : FiniteCurrentMassBridgeInputs)
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


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooExistsLowerUpper
    (I : FiniteCurrentMassBridgeInputs)
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


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (I : FiniteCurrentMassBridgeInputs)
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


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
      C hagree hβc hlower hupper)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCLowerBoundExistsNoWindowUpperExists
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkBetaCLowerBoundExistsNoWindowUpperExists
      C hagree hβeq hβc hlower hupper)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkBetaCIooSandwich
      C hagree hβeq hβc hsand)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkBetaCIooSandwich_congr_predictedExponent
      C D hpred hagree hβeq hβc hsand)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCPullbackIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCPullbackIooSandwich
      C hagree hβeq hβc hpull)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCPullbackIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCPullbackIooSandwich_congr_predictedExponent
      C D hpred hagree hβeq hβc hpull)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCCanonicalWindowPullbackIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCCanonicalWindowPullbackIooSandwich
      C hagree hβeq hβc hcanon)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCCanonicalWindowPullbackIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCCanonicalWindowPullbackIooSandwich_congr_predictedExponent
      C D hpred hagree hβeq hβc hcanon)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedIooSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        C I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCSelectedIooSandwich
      C hagree hβeq hβc hp)

set_option linter.style.longLine false in


theorem ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedIooSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        D I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCSelectedIooSandwich_congr_predictedExponent
      C D hpred hagree hβeq hβc hp)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpper
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpper
      C hagree hβeq hβc hselected hlower hupper)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExists
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpperExists
      C hagree hβeq hβc hselected hlower hupper)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpper_congr_predictedExponent
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpper_congr_predictedExponent
      C D hpred hagree hβeq hβc hselected hlower hupper)

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExists_congr_predictedExponent
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
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_from_freeMassPowerLawToPlusTarget
    C
    (I.freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementLowerUpperExists_congr_predictedExponent
      C D hpred hagree hβeq hβc hselected hlower hupper)

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementExactPowerLaw
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    C hagree I.massBridge hβeq hβc hselected hexact

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogAffine
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementExactPowerLaw
    I C hagree hβeq hβc hselected
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_logAffineNearCritical
      C hselected.fkMass hlog)

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree I.massBridge hβeq hβc hselected hratio

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich
    C hagree I.massBridge hβeq hβc hselected hsand

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetEventuallyLengthEq
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
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
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetEventuallyLengthEq
    C hagree I.massBridge hβeq hβc T hisingLength

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetLengthEq
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          I.massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCFKMassPowerLawTargetLengthEq
    C hagree I.massBridge hβeq hβc T hisingLength

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumDoubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumDoubledBoxPolynomialProjection
          hlim hdecay hfinite hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumDoubledBoxPolynomialProjection
      hlim hdecay hfinite hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonDoubledBoxPolynomialProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubledBoxPolynomialProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonDoubledBoxPolynomialProjection
          hlim hdecay hSimon hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonDoubledBoxPolynomialProjection
      hlim hdecay hSimon hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeCoordinateStepBranches
          hlim hdecay hfinite hstrict hdiag).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeCoordinateStepBranches
      hlim hdecay hfinite hstrict hdiag)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeCoordinateStepBranches
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeStrictSectorCoordinateStepPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDiagonalCoordinateStepPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeCoordinateStepBranches
          hlim hdecay hSimon hstrict hdiag).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeCoordinateStepBranches
      hlim hdecay hSimon hstrict hdiag)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
          hlim hdecay hfinite hstrict hdiag hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
      hlim hdecay hfinite hstrict hdiag hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrict :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorCoordinateComparisonPositiveSubcritical)
    (hdiag :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalCoordinateComparisonPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
          hlim hdecay hSimon hstrict hdiag hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateComparisonsProfileDoubleScale
      hlim hdecay hSimon hstrict hdiag hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hone :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
          hlim hdecay hfinite hone hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
      hlim hdecay hfinite hone hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hone :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
          hlim hdecay hSimon hone hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentProfileDoubleScale
      hlim hdecay hSimon hone hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
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
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
          hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
      hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
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
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
          hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesProfileDoubleScale
      hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
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
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
          hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
      hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
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
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
          hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesProfileDoubleScale
      hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
          hlim hdecay hfinite honeLocal hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
      hlim hdecay hfinite honeLocal hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (honeLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
          hlim hdecay hSimon honeLocal hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScale
      hlim hdecay hSimon honeLocal hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
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
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
          hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
      hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
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
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
          hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullCoordinateCasesLocalProfileDoubleScale
      hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
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
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
          hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
      hlim hdecay hfinite hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
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
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
          hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorCasesLocalProfileDoubleScale
      hlim hdecay hSimon hstrictZ hdiagY hstrictY hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
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
          FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
          hlim hdecay hfiniteAt honeLocal hprofileAt).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
      hlim hdecay hfiniteAt honeLocal hprofileAt)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
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
          FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisAt β hβpos n)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
          hlim hdecay hSimonAt honeLocal hprofileAt).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonAtPositiveXFaceOrderedWedgeFullOneEdgeDescentLocalProfileDoubleScaleAt
      hlim hdecay hSimonAt honeLocal hprofileAt)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfinite :
      FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical)
    (hstrictLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
          hlim hdecay hfinite hstrictLocal hdiagLocal hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteFKSimonFreeSumPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
      hlim hdecay hfinite hstrictLocal hdiagLocal hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_finiteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical)
    (hstrictLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagLocal :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
          hlim hdecay hSimon hstrictLocal hdiagLocal hprofile).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFiniteIsingSimonPositiveXFaceOrderedWedgeFullPredecessorLocalComparisonsProfileDoubleScale
      hlim hdecay hSimon hstrictLocal hdiagLocal hprofile)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2ExactRestrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2ExactPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFreeFVQ2ExactRestrictedCylinderComparison hcmp hdecay).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFreeFVQ2ExactRestrictedCylinderComparison hcmp hdecay)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2SubexpRestrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2SubexpPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFreeFVQ2SubexpRestrictedCylinderComparison hcmp hdecay).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFreeFVQ2SubexpRestrictedCylinderComparison hcmp hdecay)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedRestrictedCylinderComparison
    (hcmp : FreeQ2PositiveSubcriticalRestrictedCylinderComparisonBelowBetaC)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFreeFVQ2TwoSidedRestrictedCylinderComparison hcmp hdecay).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFreeFVQ2TwoSidedRestrictedCylinderComparison hcmp hdecay)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_boundaryGhostComparisonProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hfixed : FreeQ2FixedInnerTwoSidedPositiveSubcritical)
    (hcomparison : FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofBoundaryGhostComparisonProjection
          hlim hfixed hcomparison hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofBoundaryGhostComparisonProjection
      hlim hfixed hcomparison hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_boundaryGhostFirstExitPositiveProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofBoundaryGhostFirstExitPositiveProjection
          hlim hdecay hfirst hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofBoundaryGhostFirstExitPositiveProjection
      hlim hdecay hfirst hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_boxGeometryComponentThirdsAbsorptionProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hthirds :
      BoundaryCrossingCapComponentThirdsAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofBoxGeometryComponentThirdsAbsorptionProjection
          hlim hdecay hthirds hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofBoxGeometryComponentThirdsAbsorptionProjection
      hlim hdecay hthirds hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare : BoundaryCrossingCapBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofBoxRatioComponentShareProjection
          hlim hdecay hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofBoxRatioComponentShareProjection
      hlim hdecay hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hsum : BoundaryCrossingCapBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofBoxRatioComponentSumProjection
          hlim hdecay hsum hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofBoxRatioComponentSumProjection
      hlim hdecay hsum hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentShareProjection
    {capBound : BoundaryCrossingCapBound}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcap : BoundaryCrossingCapUpperBoundPositiveSubcritical capBound)
    (hshare :
      BoundaryCrossingCapBoxRatioComponentShareWithBoundPositiveSubcritical
        capBound)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofCapBoundBoxRatioComponentShareProjection
          hlim hdecay hcap hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofCapBoundBoxRatioComponentShareProjection
      hlim hdecay hcap hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentSumProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofCapBoundBoxRatioComponentSumProjection
          hlim hdecay hcap hcapNonneg hsum hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofCapBoundBoxRatioComponentSumProjection
      hlim hdecay hcap hcapNonneg hsum hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_boxRatioComponentThirdsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofBoxRatioComponentThirdsProjection
          hlim hdecay hone hboundary hempty hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofBoxRatioComponentThirdsProjection
      hlim hdecay hone hboundary hempty hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_capBoundBoxRatioComponentsProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofCapBoundBoxRatioComponentsProjection
          hlim hdecay hcap hone hboundary hempty hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofCapBoundBoxRatioComponentsProjection
      hlim hdecay hcap hone hboundary hempty hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
          hlim hdecay hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
      hlim hdecay hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
          hlim hdecay hsum hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
      hlim hdecay hsum hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
          hlim hdecay hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
      hlim hdecay hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffProjection
          hlim hdecay hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffProjection
      hlim hdecay hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioCapBudgetUncutoffProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffProjection
    {capBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffPositiveSubcritical
        capBudget)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioCapBudgetScheduleUncutoffProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdUncutoffPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdUncutoffPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
          hlim hdecay hone hboundary hempty hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
      hlim hdecay hone hboundary hempty hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_sourceSectorMultiplicitySquareBoxRatioComponentsProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hone :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioOnePointCurrentRatioThirdPositiveSubcritical)
    (hboundary :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryPairCurrentRatioThirdPositiveSubcritical)
    (hempty : BoundaryCrossingCapBoxRatioEmptyBoundaryThirdPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofSourceSectorMultiplicitySquareBoxRatioComponentsProjection
          hlim hdecay hone hboundary hempty hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofSourceSectorMultiplicitySquareBoxRatioComponentsProjection
      hlim hdecay hone hboundary hempty hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentsProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentsProjection
          hlim hdecay hmajor hone hboundary hempty hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentsProjection
      hlim hdecay hmajor hone hboundary hempty hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSharePositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
          hlim hdecay hmajor hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentShareProjection
      hlim hdecay hmajor hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsum :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
          hlim hdecay hmajor hsum hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumProjection
      hlim hdecay hmajor hsum hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (h :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
          hlim hdecay hmajor h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioComponentSumUncutoffCombinedProjection
      hlim hdecay hmajor h hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hshare :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
          hlim hdecay hmajor hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffProjection
      hlim hdecay hmajor hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_decrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
          hlim hdecay hmajor hone hboundary hempty hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofDecrementedSourceProfileMajorizationSourceSectorMultiplicitySquareBoxRatioUncutoffComponentsProjection
      hlim hdecay hmajor hone hboundary hempty hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15CanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15CanonicalRatioShareSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15CanonicalRatioShareSumProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15CanonicalRatioShareSumProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15StrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictCanonicalRatioShareSumPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15StrictCanonicalRatioShareSumProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15StrictCanonicalRatioShareSumProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15ComponentDenominatorFreeSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15ComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15ComponentDenominatorFreeSumProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15ComponentDenominatorFreeSumProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15AggregateComponentShareProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15AggregateComponentShareProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareScheduleProjection
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorptionPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15AggregateComponentShareScheduleProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15AggregateComponentShareScheduleProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15AggregateComponentShareScheduleComponentsProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15AggregateComponentShareScheduleComponentsProjection
          hlim hdecay hbudget hone hboundary hempty hshell hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15AggregateComponentShareScheduleComponentsProjection
      hlim hdecay hbudget hone hboundary hempty hshell hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15BoundaryCrossingRemainderProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15BoundaryCrossingRemainderProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderStrictProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15BoundaryCrossingRemainderStrictProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15BoundaryCrossingRemainderStrictProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15StrictComponentDenominatorFreeSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictComponentDenominatorFreeSumAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15StrictComponentDenominatorFreeSumProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15StrictComponentDenominatorFreeSumProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hstrict :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hshare :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSumProjection
          hlim hdecay hstrict hshare hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualThresholdShellBudget15BoundaryCrossingRemainderShareComponentStrictCanonicalRatioShareSumProjection
      hlim hdecay hstrict hshare hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionBudgetTailStrictRemainderDenominatorFreeProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeProjection
          hlim hdecay h hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionBudgetTailStrictRemainderDenominatorFreeProjection
      hlim hdecay h hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionComponentBudgetScheduleComponentsProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionComponentBudgetScheduleComponentsProjection
          hlim hdecay hremaining htail hsingleton hpayment
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionComponentBudgetScheduleComponentsProjection
      hlim hdecay hremaining htail hsingleton hpayment hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonProjection
          hlim hdecay hremaining htail hpayment hsingletonResidual
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionComponentBudgetScheduleNamedResidualCaseSingletonProjection
      hlim hdecay hremaining htail hpayment hsingletonResidual hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignProjection
          hlim hdecay hR hstrict hremaining htail hsingletonResidual
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionShareScheduleResidualCaseSingletonPaymentDerivedSignProjection
      hlim hdecay hR hstrict hremaining htail hsingletonResidual hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSignProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSignProjection
          hlim hdecay hR hstrict hremaining htail hsingletonResidual
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionShareScheduleResidualCaseSingletonDenominatorNonnegativeDerivedSignProjection
      hlim hdecay hR hstrict hremaining htail hsingletonResidual hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPaymentProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPaymentProjection
          hlim hdecay hR hstrict hremaining htail hpayment hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsNamedPaymentProjection
      hlim hdecay hR hstrict hremaining htail hpayment hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_liveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPaymentProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPaymentProjection
          hlim hdecay hR hstrict hremaining htail hpayment hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofLiveSingletonOptionShareScheduleResidualCaseNormalizedLabelRowsNamedPaymentProjection
      hlim hdecay hR hstrict hremaining htail hpayment hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_logRatioLimit
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_logRatioLimit
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hratio

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_powerSandwich
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_powerSandwich
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hpow

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerUpper
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerUpper
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooExistsLowerUpper
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooExistsLowerUpper
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerBoundExistsUpperExists
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsUpperExists
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_constantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβc hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkBetaCIooSandwich
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkBetaCIooSandwich
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβeq hβc hsand

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCPullbackIooSandwich
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCPullbackIooSandwich
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβeq hβc hpull

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCCanonicalWindowPullbackIooSandwich
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCCanonicalWindowPullbackIooSandwich
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβeq hβc hcanon

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedIooSandwich
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedIooSandwich
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβeq hβc hp

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedAgreementLowerUpper
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge)
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
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpper
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβeq hβc hselected hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection_fkPCSelectedAgreementLowerUpperExists
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
          hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp
          hprojection).massBridge)
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
  ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLowerUpperExists
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRawProfilePaymentActualSchedulePaymentsAllowedEmptyComparisonProjection
      hlim hdecay hR hrawStrict hrawPayment hone hboundary hcmp hprojection)
    C hagree hβeq hβc hselected hlower hupper

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalProjection
          hlim hdecay hR hraw hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalProjection
      hlim hdecay hR hraw hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalProjection
          hlim hdecay hR hraw hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalProjection
      hlim hdecay hR hraw hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositiveProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hpos :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderPositivePositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositiveProjection
          hlim hdecay hpos hraw hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalRemainderPositiveProjection
      hlim hdecay hpos hraw hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hpaid :
      BoundaryCrossingCapComponentStrictCanonicalRatioShareSumPositiveSubcritical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical)
    (hprojection :
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
          hlim hdecay hpaid hraw hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
      hlim hdecay hpaid hraw hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositiveProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositiveProjection
          hlim hdecay hpos hraw hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalRemainderPositiveProjection
      hlim hdecay hpos hraw hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_residualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
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
      FreeQ2BoundaryFreeVertexDoubleScaleProjectionPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
          hlim hdecay hpaid hraw hprojection).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofResidualCaseNormalizedLabelRowsCanonicalRawStrictTotalComponentStrictCanonicalRatioShareSumProjection
      hlim hdecay hpaid hraw hprojection)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
          hlim hdecay hcompare).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogAffine
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
          hlim hdecay hcompare).massBridge)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogAffine
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hβeq hβc hselected hlog

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogRatioLimit
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
          hlim hdecay hcompare).massBridge)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hβeq hβc hselected hratio

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementLogRatioSandwich
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
          hlim hdecay hcompare).massBridge)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioSandwich
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hβeq hβc hselected hsand

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCSelectedAgreementExactPowerLaw
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
          hlim hdecay hcompare).massBridge)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementExactPowerLaw
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hβeq hβc hselected hexact

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCFKMassPowerLawTargetEventuallyLengthEq
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass
            (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
              hlim hdecay hcompare).massBridge β) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetEventuallyLengthEq
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hβeq hβc T hisingLength

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis_fkPCFKMassPowerLawTargetLengthEq
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (hcompare :
      FreeQ2BoundaryVertexFiniteVolumePolynomialComparisonToXAxisPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass
          (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
            hlim hdecay hcompare).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetLengthEq
    (ofFreeFVQ2TwoSidedFiniteVolumePolynomialComparisonToXAxis
      hlim hdecay hcompare)
    C hagree hβeq hβc T hisingLength

set_option linter.style.longLine false in


theorem
    ising3D_liminfCorrelationLength_hasCriticalNu_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C
        (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper
          hlim hdecay htension).massBridge) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  ising3D_liminfCorrelationLength_hasCriticalNu
    (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper hlim hdecay htension)
    C hagree hpower

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper_fkPCSelectedAgreementExactPowerLaw
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper
          hlim hdecay htension).massBridge)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementExactPowerLaw
    (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper hlim hdecay htension)
    C hagree hβeq hβc hselected hexact

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_freeFVQ2TwoSidedActualConvexSurfaceTensionUpper_fkPCFKMassPowerLawTargetEventuallyLengthEq
    (hlim : FreeIsingThermodynamicLimitPositiveSubcritical)
    (hdecay : FreeFVQ2TwoSidedPositiveSubcritical)
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass
            (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper
              hlim hdecay htension).massBridge β) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCFKMassPowerLawTargetEventuallyLengthEq
    (ofFreeFVQ2TwoSidedActualConvexSurfaceTensionUpper hlim hdecay htension)
    C hagree hβeq hβc T hisingLength

end FiniteCurrentMassBridgeInputs
end Exact3D
end StatMech
