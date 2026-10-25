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
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part18


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree hmass hβeq hβc hselected hratio).rgToExponentBridge_liminfCorrelationLength

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree hmass hβeq hβc hselected hratio).hasCriticalNu_liminfCorrelationLength

set_option linter.style.longLine false in


theorem rgToExponentBridge_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical
        C hselected.fkMass) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich
    C hagree hmass hβeq hβc hselected hsand).rgToExponentBridge_liminfCorrelationLength

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical
        C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  (freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioSandwich
    C hagree hmass hβeq hβc hselected hsand).hasCriticalNu_liminfCorrelationLength

end Exact3D
end StatMech
