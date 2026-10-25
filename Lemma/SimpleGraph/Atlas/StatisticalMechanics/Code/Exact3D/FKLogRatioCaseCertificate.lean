import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.FKLogRatioCaseCertificate.Part8
open StatMech StatMech.Exact3D StatMech.Exact3D.FKLogRatioCaseCertificate


/--
[exactMonomialFKMass_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma exactMonomialFKMass_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
-- given
  (hpred : C.predictedExponent = D.predictedExponent) :
-- imply
  exactMonomialFKMass C = exactMonomialFKMass D := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.exactMonomialFKMass_congr_predictedExponent C D hpred

/--
[logRatioValue_exactMonomialFKMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma logRatioValue_exactMonomialFKMass_eq
  {C : RGCertificate Ising3DModel}
  {p : ℝ}
-- given
  (hp : p ∈ Set.Ioo (Ising3DFKPC - (1 : ℝ) / 2) Ising3DFKPC) :
-- imply
  logRatioValue (exactMonomialFKMass C) p = C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.logRatioValue_exactMonomialFKMass C hp

/--
[constantPrefactorMonomialFKMass_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma constantPrefactorMonomialFKMass_congr_predictedExponent_eq
  {C D : RGCertificate Ising3DModel}
  {A : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent) :
-- imply
  constantPrefactorMonomialFKMass C A = constantPrefactorMonomialFKMass D A := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.constantPrefactorMonomialFKMass_congr_predictedExponent C D A hpred

/--
[logRatioValue_constantPrefactorMonomialFKMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma logRatioValue_constantPrefactorMonomialFKMass_eq
  {C : RGCertificate Ising3DModel}
  {A p : ℝ}
-- given
  (hA : 0 < A)
  (hp : p ∈ Set.Ioo (Ising3DFKPC - (1 : ℝ) / 2) Ising3DFKPC) :
-- imply
  logRatioValue (constantPrefactorMonomialFKMass C A) p = C.predictedExponent + Real.log A / Real.log (Ising3DFKPC - p) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.logRatioValue_constantPrefactorMonomialFKMass C hA hp

/--
[eventually_logRatioValue_constantPrefactorMonomialFKMass_halfSlack](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma eventually_logRatioValue_constantPrefactorMonomialFKMass_halfSlack_eq
  {C : RGCertificate Ising3DModel}
  {A ε : ℝ}
-- given
  (hA : 0 < A)
  (hε : 0 < ε) :
-- imply
  ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC), C.predictedExponent - ε / 2 < logRatioValue (constantPrefactorMonomialFKMass C A) p ∧ logRatioValue (constantPrefactorMonomialFKMass C A) p < C.predictedExponent + ε / 2 := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.eventually_logRatioValue_constantPrefactorMonomialFKMass_halfSlack C hA hε

/--
[hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementCaseCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementCaseCertificate_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
  [DecidableEq Case]
  {H : Certificate C hselected.fkMass Case}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementCaseCertificate I C hagree hβeq hβc hselected H

/--
[hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementVaryingCaseCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementVaryingCaseCertificate_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
  {H : VaryingCertificate C hselected.fkMass}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselected : FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical I.massBridge) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_fkPCSelectedAgreementVaryingCaseCertificate I C hagree hβeq hβc hselected H

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
  [DecidableEq Case]
  {H : Certificate C fkMass Case}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate I C hagree hβeq hβc hselectedEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementVaryingCaseCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementVaryingCaseCertificate_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
  {H : VaryingCertificate C fkMass}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementVaryingCaseCertificate I C hagree hβeq hβc hselectedEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hratio : FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit I C hagree hβeq hβc hselectedEq hratio

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioSandwich_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hsand : FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioSandwich I C hagree hβeq hβc hselectedEq hsand

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementAsymptoticPowerLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementAsymptoticPowerLaw_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hasymp : FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical C fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementAsymptoticPowerLaw I C hagree hβeq hβc hselectedEq hasymp

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hratio : FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical D fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent I C D hpred hagree hβeq hβc hselectedEq hratio

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hsand : FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical D fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent I C D hpred hagree hβeq hβc hselectedEq hsand

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hasymp : FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical D fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent I C D hpred hagree hβeq hβc hselectedEq hasymp

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
  [DecidableEq Case]
  {H : Certificate D fkMass Case}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementCaseCertificate_congr_predictedExponent I C D hpred hagree hβeq hβc hselectedEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementVaryingCaseCertificate_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementVaryingCaseCertificate_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
  {H : VaryingCertificate D fkMass}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementVaryingCaseCertificate_congr_predictedExponent I C D hpred hagree hβeq hβc hselectedEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementExactMonomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementExactMonomial_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = exactMonomialFKMass C (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementExactMonomial I C hagree hβeq hβc hselectedEq

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementConstantPrefactorMonomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementConstantPrefactorMonomial_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
  {A : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hA : 0 < A)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = constantPrefactorMonomialFKMass C A (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementConstantPrefactorMonomial I C hagree hβeq hβc hA hselectedEq

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementExactMonomial_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementExactMonomial_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = exactMonomialFKMass D (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementExactMonomial_congr_predictedExponent I C D hpred hagree hβeq hβc hselectedEq

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
  {A : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hA : 0 < A)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = constantPrefactorMonomialFKMass D A (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent I C D hpred hagree hβeq hβc hA hselectedEq

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqCaseCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqCaseCertificate_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass modelMass : ℝ → ℝ}
  [DecidableEq Case]
  {H : Certificate C modelMass Case}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hMassEq : ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC), fkMass p = modelMass p) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqCaseCertificate I C hagree hβeq hβc hselectedEq hMassEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqCaseCertificate_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqCaseCertificate_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass modelMass : ℝ → ℝ}
  [DecidableEq Case]
  {H : Certificate D modelMass Case}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hMassEq : ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC), fkMass p = modelMass p) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqCaseCertificate_congr_predictedExponent I C D hpred hagree hβeq hβc hselectedEq hMassEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass modelMass : ℝ → ℝ}
  {H : VaryingCertificate C modelMass}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hMassEq : ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC), fkMass p = modelMass p) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate I C hagree hβeq hβc hselectedEq hMassEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_congr_predictedExponent_eq
  {I : FiniteCurrentMassBridgeInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass modelMass : ℝ → ℝ}
  {H : VaryingCertificate D modelMass}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
  (hβc : 0 < Ising.betaC 3)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hMassEq : ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC), fkMass p = modelMass p) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_congr_predictedExponent I C D hpred hagree hβeq hβc hselectedEq hMassEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
  [DecidableEq Case]
  {H : Certificate C fkMass Case}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate I C hagree htransition hnonpos hselectedEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
  {H : VaryingCertificate C fkMass}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate I C hagree htransition hnonpos hselectedEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate_congr_predictedExponent_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
  [DecidableEq Case]
  {H : Certificate D fkMass Case}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate_congr_predictedExponent I C D hpred hagree htransition hnonpos hselectedEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate_congr_predictedExponent_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
  {H : VaryingCertificate D fkMass}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate_congr_predictedExponent I C D hpred hagree htransition hnonpos hselectedEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hratio : FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit I C hagree htransition hnonpos hselectedEq hratio

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hsand : FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich I C hagree htransition hnonpos hselectedEq hsand

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hasymp : FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical C fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw I C hagree htransition hnonpos hselectedEq hasymp

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hratio : FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical D fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent I C D hpred hagree htransition hnonpos hselectedEq hratio

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hsand : FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical D fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent I C D hpred hagree htransition hnonpos hselectedEq hsand

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass : ℝ → ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hasymp : FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical D fkMass) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent I C D hpred hagree htransition hnonpos hselectedEq hasymp

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = exactMonomialFKMass C (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial I C hagree htransition hnonpos hselectedEq

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
  {A : ℝ}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hA : 0 < A)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = constantPrefactorMonomialFKMass C A (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial I C hagree htransition hnonpos hA hselectedEq

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial_congr_predictedExponent_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C D : RGCertificate Ising3DModel}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = exactMonomialFKMass D (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial_congr_predictedExponent I C D hpred hagree htransition hnonpos hselectedEq

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C D : RGCertificate Ising3DModel}
  {A : ℝ}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hA : 0 < A)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = constantPrefactorMonomialFKMass D A (IsingFK.pOfBeta β)) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent I C D hpred hagree htransition hnonpos hA hselectedEq

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass modelMass : ℝ → ℝ}
  [DecidableEq Case]
  {H : Certificate C modelMass Case}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hMassEq : ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC), fkMass p = modelMass p) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate I C hagree htransition hnonpos hselectedEq hMassEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate_congr_predictedExponent_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass modelMass : ℝ → ℝ}
  [DecidableEq Case]
  {H : Certificate D modelMass Case}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hMassEq : ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC), fkMass p = modelMass p) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate_congr_predictedExponent I C D hpred hagree htransition hnonpos hselectedEq hMassEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C : RGCertificate Ising3DModel}
  {fkMass modelMass : ℝ → ℝ}
  {H : VaryingCertificate C modelMass}
-- given
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hMassEq : ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC), fkMass p = modelMass p) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate I C hagree htransition hnonpos hselectedEq hMassEq H

/--
[hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_congr_predictedExponent_eq
  {I : FiniteCurrentActualScheduleProjectionInputs}
  {C D : RGCertificate Ising3DModel}
  {fkMass modelMass : ℝ → ℝ}
  {H : VaryingCertificate D modelMass}
-- given
  (hpred : C.predictedExponent = D.predictedExponent)
  (hagree : PlusFreeTwoPointAgreeBelowBetaC)
  (htransition : Ising3DTransitionAssemblyInputs)
  (hnonpos : Ising3DNoPositiveMagnetizationAtNonpositiveBeta)
  (hselectedEq : ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC), freeSelectedPositiveSubcriticalMass I.massBridge β = fkMass (IsingFK.pOfBeta β))
  (hMassEq : ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC), fkMass p = modelMass p) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) (Real.log C.scale.toReal / Real.log C.thermalEigenvalue) := by
-- proof
  apply StatMech.Exact3D.FKLogRatioCaseCertificate.hasCriticalNu_liminfCorrelationLength_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_congr_predictedExponent I C D hpred hagree htransition hnonpos hselectedEq hMassEq H


-- created on 2026-10-23
