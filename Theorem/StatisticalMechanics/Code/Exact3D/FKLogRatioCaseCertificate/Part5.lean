/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.FKLogRatioCaseCertificate.Part7


namespace StatMech

namespace Exact3D

namespace FKLogRatioCaseCertificate

open FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementVaryingCaseCertificate_congr_predictedExponent
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
    (H : VaryingCertificate D fkMass) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementVaryingCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in

theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementExactMonomial
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass C (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (exactMonomialCertificate C)

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementConstantPrefactorMonomial
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
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
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (constantPrefactorMonomialCertificate C hA)

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementExactMonomial_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass D (IsingFK.pOfBeta β)) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementExactMonomial
    I C hagree hβeq hβc
    (by
      have hmass := exactMonomialFKMass_congr_predictedExponent C D hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent
    (I : FiniteCurrentMassBridgeInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
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
      C.predictedExponent :=
  hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementConstantPrefactorMonomial
    I C hagree hβeq hβc hA
    (by
      have hmass :=
        constantPrefactorMonomialFKMass_congr_predictedExponent C D A hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in


theorem hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
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
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C modelMass Case) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected
    (logRatioLimit_of_eventuallyEq C fkMass modelMass H hMassEq)

end FKLogRatioCaseCertificate
end Exact3D
end StatMech
