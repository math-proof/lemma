/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.FKLogRatioCaseCertificate.Part10


namespace StatMech

namespace Exact3D

namespace FKLogRatioCaseCertificate

open FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    (H : VaryingCertificate D modelMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    I C hagree hβeq hβc hselectedEq hMassEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
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
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected
    (logRatioLimit C fkMass H)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
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
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected
    (logRatioLimitVarying C fkMass H)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    {Case : Type*} [DecidableEq Case]
    (H : Certificate D fkMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree htransition hnonpos hselectedEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (H : VaryingCertificate D fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate
    I C hagree htransition hnonpos hselectedEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
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
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected hratio

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
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
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioSandwichTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected hsand

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
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
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    I C hagree htransition hnonpos hselectedEq
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_asymptoticPowerLaw
      C fkMass hasymp)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
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
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    I C hagree htransition hnonpos hselectedEq
    (hratio.congr_predictedExponent hpred)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
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
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich
    I C hagree htransition hnonpos hselectedEq
    (hsand.congr_predictedExponent hpred)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
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
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw
    I C hagree htransition hnonpos hselectedEq
    (hasymp.congr_predictedExponent hpred)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass C (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree htransition hnonpos hselectedEq
    (exactMonomialCertificate C)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {A : ℝ}
    (hA : 0 < A)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          constantPrefactorMonomialFKMass C A (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree htransition hnonpos hselectedEq
    (constantPrefactorMonomialCertificate C hA)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass D (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial
    I C hagree htransition hnonpos
    (by
      have hmass := exactMonomialFKMass_congr_predictedExponent C D hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {A : ℝ}
    (hA : 0 < A)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          constantPrefactorMonomialFKMass D A (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial
    I C hagree htransition hnonpos hA
    (by
      have hmass :=
        constantPrefactorMonomialFKMass_congr_predictedExponent C D A hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C modelMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected
    (logRatioLimit_of_eventuallyEq C fkMass modelMass H hMassEq)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate D modelMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate
    I C hagree htransition hnonpos hselectedEq hMassEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    (H : VaryingCertificate C modelMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.ising3D_liminfCorrelationLength_hasCriticalNu_of_fkPCSelectedAgreementLogRatioLimitTransitionAssemblyNonpositiveBeta
    I C hagree htransition hnonpos hselected
    (logRatioLimitVarying_of_eventuallyEq C fkMass modelMass H hMassEq)

set_option linter.style.longLine false in


theorem
    hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (htransition : Ising3DTransitionAssemblyInputs)
    (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
    {fkMass modelMass : ℝ → ℝ}
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          fkMass (IsingFK.pOfBeta β))
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p)
    (H : VaryingCertificate D modelMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) :=
  hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    I C hagree htransition hnonpos hselectedEq hMassEq
    (H.congr_predictedExponent hpred)

end FKLogRatioCaseCertificate
end Exact3D
end StatMech
