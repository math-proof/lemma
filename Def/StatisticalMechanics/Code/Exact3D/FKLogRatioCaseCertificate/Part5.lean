/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.FKLogRatioCaseCertificate.Part2


namespace StatMech

namespace Exact3D

namespace FKLogRatioCaseCertificate

open FiniteCurrentMassBridgeInputs

set_option linter.style.longLine false in


noncomputable def constantPrefactorMonomialEpsilonTable
    (C : RGCertificate Ising3DModel)
    {A : ℝ}
    (hA : 0 < A)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    EpsilonTable C (constantPrefactorMonomialFKMass C A) Unit epsilon := by
  classical
  have hlowerGap :
      C.predictedExponent - epsilon <
        C.predictedExponent - epsilon / 2 := by
    linarith
  let lowerRat : ℚ := Classical.choose (exists_rat_btwn hlowerGap)
  have hlowerRat_spec :
      C.predictedExponent - epsilon < (lowerRat : ℝ) ∧
        (lowerRat : ℝ) < C.predictedExponent - epsilon / 2 := by
    simpa [lowerRat] using Classical.choose_spec (exists_rat_btwn hlowerGap)
  have hupperGap :
      C.predictedExponent + epsilon / 2 <
        C.predictedExponent + epsilon := by
    linarith
  let upperRat : ℚ := Classical.choose (exists_rat_btwn hupperGap)
  have hupperRat_spec :
      C.predictedExponent + epsilon / 2 < (upperRat : ℝ) ∧
        (upperRat : ℝ) < C.predictedExponent + epsilon := by
    simpa [upperRat] using Classical.choose_spec (exists_rat_btwn hupperGap)
  have hband :=
    eventually_logRatioValue_constantPrefactorMonomialFKMass_halfSlack
      C hA hepsilon
  let window : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hband)
  have hwindow_spec :
      0 < window ∧
        ∀ p, p ∈ Set.Ioo (Ising3DFKPC - window) Ising3DFKPC →
          C.predictedExponent - epsilon / 2 <
              logRatioValue (constantPrefactorMonomialFKMass C A) p ∧
            logRatioValue (constantPrefactorMonomialFKMass C A) p <
              C.predictedExponent + epsilon / 2 := by
    simpa [window] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hband)
  let interval : RatInterval :=
    { lower := lowerRat
      upper := upperRat
      lower_le_upper := by
        have hreal : (lowerRat : ℝ) < (upperRat : ℝ) := by
          linarith [hlowerRat_spec.2, hupperRat_spec.1]
        exact_mod_cast le_of_lt hreal }
  exact
    { table :=
        { cases := {()}
          interval := fun _ => interval }
      classify := fun _ => ()
      window := window
      window_pos := hwindow_spec.1
      covers_on_Ioo := by
        intro _ _
        simp
      sound_on_Ioo := by
        intro p hp
        have hpband := hwindow_spec.2 p hp
        dsimp [interval]
        exact ⟨le_of_lt (lt_trans hlowerRat_spec.2 hpband.1),
          le_of_lt (lt_trans hpband.2 hupperRat_spec.1)⟩
      lower_inside_slack := by
        intro _ _
        simpa [interval] using hlowerRat_spec.1
      upper_inside_slack := by
        intro _ _
        simpa [interval] using hupperRat_spec.2 }

set_option linter.style.longLine false in


noncomputable def constantPrefactorMonomialCertificate
    (C : RGCertificate Ising3DModel)
    {A : ℝ}
    (hA : 0 < A) :
    Certificate C (constantPrefactorMonomialFKMass C A) Unit where
  pδ := (1 : ℝ) / 2
  pδ_pos := by norm_num
  fkMass_pos := by
    intro _ _
    exact mul_pos hA (Real.exp_pos _)
  epsilonTable := constantPrefactorMonomialEpsilonTable C hA

set_option linter.style.longLine false in


noncomputable def epsilonTableOfLogRatioSandwich
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    EpsilonTable C fkMass Unit epsilon := by
  classical
  have hhalf : 0 < epsilon / 2 := by positivity
  have hlowerGap :
      C.predictedExponent - epsilon <
        C.predictedExponent - epsilon / 2 := by
    linarith
  let lowerRat : ℚ := Classical.choose (exists_rat_btwn hlowerGap)
  have hlowerRat_spec :
      C.predictedExponent - epsilon < (lowerRat : ℝ) ∧
        (lowerRat : ℝ) < C.predictedExponent - epsilon / 2 := by
    simpa [lowerRat] using Classical.choose_spec (exists_rat_btwn hlowerGap)
  have hupperGap :
      C.predictedExponent + epsilon / 2 <
        C.predictedExponent + epsilon := by
    linarith
  let upperRat : ℚ := Classical.choose (exists_rat_btwn hupperGap)
  have hupperRat_spec :
      C.predictedExponent + epsilon / 2 < (upperRat : ℝ) ∧
        (upperRat : ℝ) < C.predictedExponent + epsilon := by
    simpa [upperRat] using Classical.choose_spec (exists_rat_btwn hupperGap)
  have hband := hsand.log_fk_mass_ratio_sandwich (epsilon / 2) hhalf
  let window : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hband)
  have hwindow_spec :
      0 < window ∧
        ∀ p, p ∈ Set.Ioo (Ising3DFKPC - window) Ising3DFKPC →
          C.predictedExponent - epsilon / 2 <
              logRatioValue fkMass p ∧
            logRatioValue fkMass p <
              C.predictedExponent + epsilon / 2 := by
    simpa [window, logRatioValue] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hband)
  let interval : RatInterval :=
    { lower := lowerRat
      upper := upperRat
      lower_le_upper := by
        have hreal : (lowerRat : ℝ) < (upperRat : ℝ) := by
          linarith [hlowerRat_spec.2, hupperRat_spec.1]
        exact_mod_cast le_of_lt hreal }
  exact
    { table :=
        { cases := {()}
          interval := fun _ => interval }
      classify := fun _ => ()
      window := window
      window_pos := hwindow_spec.1
      covers_on_Ioo := by
        intro _ _
        simp
      sound_on_Ioo := by
        intro p hp
        have hpband := hwindow_spec.2 p hp
        dsimp [interval]
        exact ⟨le_of_lt (lt_trans hlowerRat_spec.2 hpband.1),
          le_of_lt (lt_trans hpband.2 hupperRat_spec.1)⟩
      lower_inside_slack := by
        intro _ _
        simpa [interval] using hlowerRat_spec.1
      upper_inside_slack := by
        intro _ _
        simpa [interval] using hupperRat_spec.2 }

set_option linter.style.longLine false in


noncomputable def certificateOfLogRatioSandwich
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
    Certificate C fkMass Unit where
  pδ := hsand.pδ
  pδ_pos := hsand.pδ_pos
  fkMass_pos := hsand.fkMass_pos
  epsilonTable := epsilonTableOfLogRatioSandwich C fkMass hsand

set_option linter.style.longLine false in


noncomputable def certificateOfLogRatioLimit
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    Certificate C fkMass Unit :=
  certificateOfLogRatioSandwich C fkMass
    (freePositiveSubcriticalMassFKPCLogRatioSandwich_of_logRatioLimit
      C fkMass hratio)

set_option linter.style.longLine false in


noncomputable def logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass where
  pδ := H.pδ
  pδ_pos := H.pδ_pos
  fkMass_pos := H.fkMass_pos
  log_fk_mass_ratio_sandwich := by
    intro epsilon hepsilon
    let T := H.epsilonTable epsilon hepsilon
    filter_upwards
      [Ioo_mem_nhdsLT
        (show Ising3DFKPC - T.window < Ising3DFKPC by
          linarith [T.window_pos])] with p hp
    have hcover : T.classify p ∈ T.table.cases :=
      T.covers_on_Ioo p hp
    have hmem :
        (T.table.interval (T.classify p)).MemR (logRatioValue fkMass p) :=
      T.sound_on_Ioo p hp
    constructor
    · exact lt_of_lt_of_le
        (T.lower_inside_slack (T.classify p) hcover) hmem.1
    · exact lt_of_le_of_lt hmem.2
        (T.upper_inside_slack (T.classify p) hcover)

set_option linter.style.longLine false in


noncomputable def logRatioSandwichVarying
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (H : VaryingCertificate C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass where
  pδ := H.pδ
  pδ_pos := H.pδ_pos
  fkMass_pos := H.fkMass_pos
  log_fk_mass_ratio_sandwich := by
    intro epsilon hepsilon
    letI := H.caseDecidableEq epsilon
    let T := H.epsilonTable epsilon hepsilon
    filter_upwards
      [Ioo_mem_nhdsLT
        (show Ising3DFKPC - T.window < Ising3DFKPC by
          linarith [T.window_pos])] with p hp
    have hcover : T.classify p ∈ T.table.cases :=
      T.covers_on_Ioo p hp
    have hmem :
        (T.table.interval (T.classify p)).MemR (logRatioValue fkMass p) :=
      T.sound_on_Ioo p hp
    constructor
    · exact lt_of_lt_of_le
        (T.lower_inside_slack (T.classify p) hcover) hmem.1
    · exact lt_of_le_of_lt hmem.2
        (T.upper_inside_slack (T.classify p) hcover)

set_option linter.style.longLine false in


noncomputable def logRatioSandwich_of_eventuallyEq
    (C : RGCertificate Ising3DModel)
    (fkMass modelMass : ℝ → ℝ)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C modelMass Case)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioSandwich_of_eventuallyEq
    C (logRatioSandwich C modelMass H) hEq

set_option linter.style.longLine false in


noncomputable def logRatioSandwichVarying_of_eventuallyEq
    (C : RGCertificate Ising3DModel)
    (fkMass modelMass : ℝ → ℝ)
    (H : VaryingCertificate C modelMass)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioSandwich_of_eventuallyEq
    C (logRatioSandwichVarying C modelMass H) hEq

set_option linter.style.longLine false in


noncomputable def logRatioLimit
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
    C fkMass (logRatioSandwich C fkMass H)

set_option linter.style.longLine false in


noncomputable def logRatioLimitVarying
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (H : VaryingCertificate C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
    C fkMass (logRatioSandwichVarying C fkMass H)

set_option linter.style.longLine false in


noncomputable def logRatioLimit_of_eventuallyEq
    (C : RGCertificate Ising3DModel)
    (fkMass modelMass : ℝ → ℝ)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C modelMass Case)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioLimit_of_eventuallyEq
    C (logRatioLimit C modelMass H) hEq

set_option linter.style.longLine false in


noncomputable def logRatioLimitVarying_of_eventuallyEq
    (C : RGCertificate Ising3DModel)
    (fkMass modelMass : ℝ → ℝ)
    (H : VaryingCertificate C modelMass)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioLimit_of_eventuallyEq
    C (logRatioLimitVarying C modelMass H) hEq

set_option linter.style.longLine false in


noncomputable def logAffine
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_logRatioLimit
    C fkMass (logRatioLimit C fkMass H)

set_option linter.style.longLine false in


noncomputable def logAffineVarying
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (H : VaryingCertificate C fkMass) :
    FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_logRatioLimit
    C fkMass (logRatioLimitVarying C fkMass H)

set_option linter.style.longLine false in


noncomputable def exactPowerLaw
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioLimit
    C fkMass (logRatioLimit C fkMass H)

set_option linter.style.longLine false in


noncomputable def exactPowerLawVarying
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (H : VaryingCertificate C fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioLimit
    C fkMass (logRatioLimitVarying C fkMass H)

set_option linter.style.longLine false in


noncomputable def selectedIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C hselected.fkMass Case) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_exactPowerLaw
    C hmass hselected
    (exactPowerLaw C hselected.fkMass H)

set_option linter.style.longLine false in


noncomputable def selectedIooSandwichVarying
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (H : VaryingCertificate C hselected.fkMass) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_exactPowerLaw
    C hmass hselected
    (exactPowerLawVarying C hselected.fkMass H)

set_option linter.style.longLine false in


noncomputable def selectedIooSandwich_of_eventualMassEqCaseCertificate
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    {modelMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        hselected.fkMass p = modelMass p)
    (H : Certificate C modelMass Case) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  selectedIooSandwich C hmass hselected (H.of_eventuallyEq hMassEq)

set_option linter.style.longLine false in


noncomputable def selectedIooSandwichVarying_of_eventualMassEqCaseCertificate
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    {modelMass : ℝ → ℝ}
    (hMassEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        hselected.fkMass p = modelMass p)
    (H : VaryingCertificate C modelMass) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  selectedIooSandwichVarying C hmass hselected
    (H.of_eventuallyEq hMassEq)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementCaseCertificate
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
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree I.massBridge hβeq hβc hselected
    (logRatioLimit C hselected.fkMass H)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementVaryingCaseCertificate
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
        I.massBridge)
    (H : VaryingCertificate C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree I.massBridge hβeq hβc hselected
    (logRatioLimitVarying C hselected.fkMass H)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioLimit
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
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLogRatioLimit
    C hagree I.massBridge hβeq hβc hselected hratio

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioSandwich
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
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
      C fkMass hsand)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementAsymptoticPowerLaw
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
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_asymptoticPowerLaw
      C fkMass hasymp)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent
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
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (hratio.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent
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
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementLogRatioSandwich
    I C hagree hβeq hβc hselectedEq
    (hsand.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent
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
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementAsymptoticPowerLaw
    I C hagree hβeq hβc hselectedEq
    (hasymp.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementCaseCertificate
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
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselected H

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementVaryingCaseCertificate
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
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  freeMassPowerLawToPlusTarget_of_fkPCSelectedAgreementVaryingCaseCertificate
    I C hagree hβeq hβc hselected H

set_option linter.style.longLine false in

noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementExactMonomial
    (I : FiniteCurrentMassBridgeInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass C (IsingFK.pOfBeta β)) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (exactMonomialCertificate C)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementConstantPrefactorMonomial
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
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (constantPrefactorMonomialCertificate C hA)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementExactMonomial_congr_predictedExponent
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
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementExactMonomial
    I C hagree hβeq hβc
    (by
      have hmass := exactMonomialFKMass_congr_predictedExponent C D hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent
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
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_eventualSelectedAgreementConstantPrefactorMonomial
    I C hagree hβeq hβc hA
    (by
      have hmass :=
        constantPrefactorMonomialFKMass_congr_predictedExponent C D A hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.analyticLogRatioBridge_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected
    (by
      simpa [hselected] using logRatioLimit C fkMass H)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.analyticLogRatioBridge_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected
    (by
      simpa [hselected] using logRatioLimitVarying C fkMass H)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    {Case : Type*} [DecidableEq Case]
    (H : Certificate D fkMass Case) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (H.of_eventuallyEq hMassEq)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    (H : VaryingCertificate C modelMass) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementVaryingCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (H.of_eventuallyEq hMassEq)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    {Case : Type*} [DecidableEq Case]
    (H : Certificate D modelMass Case) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqCaseCertificate
    I C hagree hβeq hβc hselectedEq hMassEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementEventualMassEqVaryingCaseCertificate
    I C hagree hβeq hβc hselectedEq hMassEq
    (H.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  let hselected :=
    freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
      I.massBridge fkMass hselectedEq
  FiniteCurrentActualScheduleProjectionInputs.analyticLogRatioBridge_of_fkPCSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselected hratio

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
      C fkMass hsand)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_asymptoticPowerLaw
      C fkMass hasymp)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioLimit
    I C hagree hβeq hβc hselectedEq
    (hratio.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementLogRatioSandwich
    I C hagree hβeq hβc hselectedEq
    (hsand.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementAsymptoticPowerLaw
    I C hagree hβeq hβc hselectedEq
    (hasymp.congr_predictedExponent hpred)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass C (IsingFK.pOfBeta β)) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (exactMonomialCertificate C)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementCaseCertificate
    I C hagree hβeq hβc hselectedEq
    (constantPrefactorMonomialCertificate C hA)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
    (C D : RGCertificate Ising3DModel)
    (hpred : C.predictedExponent = D.predictedExponent)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselectedEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass I.massBridge β =
          exactMonomialFKMass D (IsingFK.pOfBeta β)) :
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementExactMonomial
    I C hagree hβeq hβc
    (by
      have hmass := exactMonomialFKMass_congr_predictedExponent C D hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

set_option linter.style.longLine false in


noncomputable def analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial_congr_predictedExponent
    (I : FiniteCurrentActualScheduleProjectionInputs)
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
    FiniteCurrentActualScheduleProjectionInputs.AnalyticLogRatioBridge I C :=
  analyticLogRatioBridge_of_actualScheduleProjection_eventualSelectedAgreementConstantPrefactorMonomial
    I C hagree hβeq hβc hA
    (by
      have hmass :=
        constantPrefactorMonomialFKMass_congr_predictedExponent C D A hpred
      filter_upwards [hselectedEq] with β hβ
      simpa [hmass] using hβ)

end FKLogRatioCaseCertificate
end Exact3D
end StatMech
