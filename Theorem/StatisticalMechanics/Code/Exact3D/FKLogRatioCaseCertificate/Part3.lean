/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.FKLogRatioCaseCertificate.Part5


namespace StatMech

namespace Exact3D

namespace FKLogRatioCaseCertificate

open FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C hselected.fkMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected
    (logRatioLimit C hselected.fkMass H)

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementVaryingCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (H : VaryingCertificate C hselected.fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected
    (logRatioLimitVarying C hselected.fkMass H)

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselected H

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementVaryingCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (H : VaryingCertificate C fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementVaryingCaseCertificate
    I C hagree hβeq hβc hselected H

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected hratio

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioSandwich
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioSandwich
    I C hagree hβeq hβc hselected hsand

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementAsymptoticPowerLaw
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        C fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_asymptoticPowerLaw
      C fkMass hasymp)

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical D fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (hratio.congr_predictedExponent hpred)

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical D fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioSandwich
    I C hagree hβeq hβc hselectedEq
    (hsand.congr_predictedExponent hpred)

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        D fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementAsymptoticPowerLaw
    I C hagree hβeq hβc hselectedEq
    (hasymp.congr_predictedExponent hpred)

end FKLogRatioCaseCertificate
end Exact3D
end StatMech
