/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKLogRatioCaseCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Structure.StatisticalMechanics.Code.Exact3D.FKLogRatioCaseCertificate


namespace StatMech

namespace Exact3D

namespace FKLogRatioCaseCertificate

open FiniteCurrentMassBridgeInputs

namespace EpsilonTable

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    {epsilon : ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : EpsilonTable C fkMass Case epsilon) :
    EpsilonTable D fkMass Case epsilon where
  table := T.table
  classify := T.classify
  window := T.window
  window_pos := T.window_pos
  covers_on_Ioo := T.covers_on_Ioo
  sound_on_Ioo := T.sound_on_Ioo
  lower_inside_slack := by
    intro k hk
    simpa [hpred] using T.lower_inside_slack k hk
  upper_inside_slack := by
    intro k hk
    simpa [hpred] using T.upper_inside_slack k hk

set_option linter.style.longLine false in


def restrict_window
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    {epsilon : ℝ}
    (T : EpsilonTable C fkMass Case epsilon)
    {w : ℝ} (hw : 0 < w) (hle : w ≤ T.window) :
    EpsilonTable C fkMass Case epsilon where
  table := T.table
  classify := T.classify
  window := w
  window_pos := hw
  covers_on_Ioo := by
    intro p hp
    exact T.covers_on_Ioo p
      ⟨by linarith [hp.1, hle], hp.2⟩
  sound_on_Ioo := by
    intro p hp
    exact T.sound_on_Ioo p
      ⟨by linarith [hp.1, hle], hp.2⟩
  lower_inside_slack := T.lower_inside_slack
  upper_inside_slack := T.upper_inside_slack

set_option linter.style.longLine false in


def of_globalCaseTable
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    {epsilon window : ℝ}
    (table : RatInterval.CaseTable Case)
    (classify : ℝ → Case)
    (hwindow : 0 < window)
    (hcovers : RatInterval.CaseTable.Covers table classify)
    (hsound :
      RatInterval.CaseTable.Sound table classify (logRatioValue fkMass))
    (hlower :
      ∀ k, k ∈ table.cases →
        C.predictedExponent - epsilon < ((table.interval k).lower : ℝ))
    (hupper :
      ∀ k, k ∈ table.cases →
        ((table.interval k).upper : ℝ) < C.predictedExponent + epsilon) :
    EpsilonTable C fkMass Case epsilon where
  table := table
  classify := classify
  window := window
  window_pos := hwindow
  covers_on_Ioo := fun p _hp => hcovers p
  sound_on_Ioo := fun p _hp => hsound p
  lower_inside_slack := hlower
  upper_inside_slack := hupper

end EpsilonTable

namespace Certificate

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (hpred : D.predictedExponent = C.predictedExponent)
    (H : Certificate C fkMass Case) :
    Certificate D fkMass Case where
  pδ := H.pδ
  pδ_pos := H.pδ_pos
  fkMass_pos := H.fkMass_pos
  epsilonTable := fun epsilon hepsilon =>
    (H.epsilonTable epsilon hepsilon).congr_predictedExponent hpred

set_option linter.style.longLine false in


def restrict_pδ
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case)
    {pδ' : ℝ} (hpδ' : 0 < pδ') (hle : pδ' ≤ H.pδ) :
    Certificate C fkMass Case where
  pδ := pδ'
  pδ_pos := hpδ'
  fkMass_pos := by
    intro p hp
    exact H.fkMass_pos p
      ⟨by linarith [hp.1, hle], hp.2⟩
  epsilonTable := H.epsilonTable

set_option linter.style.longLine false in


def restrict_epsilonWindows
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case)
    (window : ∀ epsilon, 0 < epsilon → ℝ)
    (hwindow_pos : ∀ epsilon hε, 0 < window epsilon hε)
    (hwindow_le :
      ∀ epsilon hε,
        window epsilon hε ≤ (H.epsilonTable epsilon hε).window) :
    Certificate C fkMass Case where
  pδ := H.pδ
  pδ_pos := H.pδ_pos
  fkMass_pos := H.fkMass_pos
  epsilonTable := fun epsilon hε =>
    (H.epsilonTable epsilon hε).restrict_window
      (hwindow_pos epsilon hε) (hwindow_le epsilon hε)

set_option linter.style.longLine false in


def restrict_windows
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C fkMass Case)
    {pδ' : ℝ} (hpδ' : 0 < pδ') (hpδ_le : pδ' ≤ H.pδ)
    (window : ∀ epsilon, 0 < epsilon → ℝ)
    (hwindow_pos : ∀ epsilon hε, 0 < window epsilon hε)
    (hwindow_le :
      ∀ epsilon hε,
        window epsilon hε ≤ (H.epsilonTable epsilon hε).window) :
    Certificate C fkMass Case :=
  (H.restrict_pδ hpδ' hpδ_le).restrict_epsilonWindows
    window hwindow_pos hwindow_le

set_option linter.style.longLine false in


def of_globalCaseTables
    {fkMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (pδ : ℝ) (hpδ : 0 < pδ)
    (hfkMass_pos :
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
        0 < fkMass p)
    (table : ∀ epsilon : ℝ, 0 < epsilon → RatInterval.CaseTable Case)
    (classify : ∀ epsilon : ℝ, 0 < epsilon → ℝ → Case)
    (windows : ∀ epsilon : ℝ, 0 < epsilon → ℝ)
    (hwindow : ∀ (epsilon : ℝ) hε, 0 < windows epsilon hε)
    (hcovers :
      ∀ (epsilon : ℝ) hε,
        RatInterval.CaseTable.Covers
          (table epsilon hε) (classify epsilon hε))
    (hsound :
      ∀ (epsilon : ℝ) hε,
        RatInterval.CaseTable.Sound
          (table epsilon hε) (classify epsilon hε)
          (logRatioValue fkMass))
    (hlower :
      ∀ (epsilon : ℝ) hε k, k ∈ (table epsilon hε).cases →
        C.predictedExponent - epsilon <
          (((table epsilon hε).interval k).lower : ℝ))
    (hupper :
      ∀ (epsilon : ℝ) hε k, k ∈ (table epsilon hε).cases →
        (((table epsilon hε).interval k).upper : ℝ) <
          C.predictedExponent + epsilon) :
    Certificate C fkMass Case where
  pδ := pδ
  pδ_pos := hpδ
  fkMass_pos := hfkMass_pos
  epsilonTable := fun epsilon hε =>
    EpsilonTable.of_globalCaseTable
      (C := C)
      (fkMass := fkMass)
      (epsilon := epsilon)
      (window := windows epsilon hε)
      (table epsilon hε)
      (classify epsilon hε)
      (hwindow epsilon hε)
      (hcovers epsilon hε)
      (hsound epsilon hε)
      (hlower epsilon hε)
      (hupper epsilon hε)

set_option linter.style.longLine false in


noncomputable def of_eventuallyEq
    {fkMass modelMass : ℝ → ℝ}
    {Case : Type*} [DecidableEq Case]
    (H : Certificate C modelMass Case)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    Certificate C fkMass Case := by
  classical
  let eqSpec := FKReparameterization.exists_Ioo_subset_of_eventually_left hEq
  let eqWindow := Classical.choose eqSpec
  have heqWindow_pos : 0 < eqWindow := (Classical.choose_spec eqSpec).1
  have heqWindow :
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC →
        fkMass p = modelMass p :=
    (Classical.choose_spec eqSpec).2
  refine
    { pδ := min H.pδ eqWindow
      pδ_pos := lt_min H.pδ_pos heqWindow_pos
      fkMass_pos := ?_
      epsilonTable := ?_ }
  · intro p hp
    have hpH : p ∈ Set.Ioo (Ising3DFKPC - H.pδ) Ising3DFKPC :=
      ⟨by linarith [hp.1, min_le_left H.pδ eqWindow], hp.2⟩
    have hpeq : p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC :=
      ⟨by linarith [hp.1, min_le_right H.pδ eqWindow], hp.2⟩
    have hEqp : fkMass p = modelMass p := heqWindow p hpeq
    simpa [hEqp] using H.fkMass_pos p hpH
  · intro epsilon hepsilon
    let T := H.epsilonTable epsilon hepsilon
    let w := min T.window eqWindow
    have hw : 0 < w := lt_min T.window_pos heqWindow_pos
    refine
      { table := T.table
        classify := T.classify
        window := w
        window_pos := hw
        covers_on_Ioo := ?_
        sound_on_Ioo := ?_
        lower_inside_slack := T.lower_inside_slack
        upper_inside_slack := T.upper_inside_slack }
    · intro p hp
      exact T.covers_on_Ioo p
        ⟨by
          have hwle : w ≤ T.window := min_le_left T.window eqWindow
          linarith [hp.1, hwle], hp.2⟩
    · intro p hp
      have hpT : p ∈ Set.Ioo (Ising3DFKPC - T.window) Ising3DFKPC :=
        ⟨by
          have hwle : w ≤ T.window := min_le_left T.window eqWindow
          linarith [hp.1, hwle], hp.2⟩
      have hpeq : p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC :=
        ⟨by
          have hwle : w ≤ eqWindow := min_le_right T.window eqWindow
          linarith [hp.1, hwle], hp.2⟩
      have hEqp : fkMass p = modelMass p := heqWindow p hpeq
      simpa [logRatioValue, hEqp] using T.sound_on_Ioo p hpT

end Certificate
end FKLogRatioCaseCertificate
end Exact3D
end StatMech
