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
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part17


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass where
  pδ := hexact.pδ
  pδ_pos := hexact.pδ_pos
  logRemainder := fun p => Real.log (hexact.massPrefactor p)
  fkMass_pos := by
    intro p hp
    rw [hexact.mass_scaling p hp]
    exact mul_pos (hexact.massPrefactor_pos p hp) (Real.exp_pos _)
  logRemainder_negligible := hexact.massPrefactor_log_negligible
  log_fk_mass_scaling := by
    intro p hp
    have hpref_pos : 0 < hexact.massPrefactor p :=
      hexact.massPrefactor_pos p hp
    have hpref_ne : hexact.massPrefactor p ≠ 0 := hpref_pos.ne'
    have hexp_ne :
        Real.exp (C.predictedExponent * Real.log (Ising3DFKPC - p)) ≠ 0 :=
      Real.exp_ne_zero _
    rw [hexact.mass_scaling p hp, Real.log_mul hpref_ne hexp_ne,
      Real.log_exp]
    ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_exactPowerLaw
    C fkMass
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_asymptoticPowerLaw
      C fkMass hasymp)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogRatioLimit_of_logAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass where
  pδ := hlog.pδ
  pδ_pos := hlog.pδ_pos
  fkMass_pos := hlog.fkMass_pos
  log_fk_mass_ratio_tendsto := by
    let L := nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC)
    have hlimit :
        Filter.Tendsto
          (fun p : ℝ =>
            C.predictedExponent +
              hlog.logRemainder p / Real.log (Ising3DFKPC - p))
          L (nhds C.predictedExponent) := by
      simpa [L] using tendsto_const_nhds.add hlog.logRemainder_negligible
    refine Filter.Tendsto.congr' ?_ hlimit
    filter_upwards
      [Ioo_mem_nhdsLT
        (show Ising3DFKPC - hlog.pδ < Ising3DFKPC by
          linarith [hlog.pδ_pos]),
        Ioo_mem_nhdsLT
          (show Ising3DFKPC - (1 : ℝ) < Ising3DFKPC by norm_num)]
      with p hpδ hpone
    have hdiff : Ising3DFKPC - p ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hpone.1, hpone.2]
    have hden : Real.log (Ising3DFKPC - p) ≠ 0 :=
      (Real.log_neg hdiff.1 hdiff.2).ne
    change
      C.predictedExponent +
          hlog.logRemainder p / Real.log (Ising3DFKPC - p) =
        Real.log (fkMass p) / Real.log (Ising3DFKPC - p)
    rw [hlog.log_fk_mass_scaling p hpδ]
    field_simp [hden]

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogRatioLimit_of_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioLimit_of_logAffineNearCritical
    C fkMass
    (freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_exactPowerLaw
      C fkMass hexact)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogRatioLimit_of_asymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hasymp :
      FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCLogRatioLimit_of_exactPowerLaw
    C fkMass
    (freePositiveSubcriticalMassFKPCExactPowerLaw_of_asymptoticPowerLaw
      C fkMass hasymp)

namespace FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical D fkMass where
  pδ := h.pδ
  pδ_pos := h.pδ_pos
  fkMass_pos := h.fkMass_pos
  log_fk_mass_ratio_tendsto := by
    simpa [hpred] using h.log_fk_mass_ratio_tendsto

end FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogRatioLimit_of_eventuallyEq
    (C : RGCertificate Ising3DModel)
    {fkMass modelMass : ℝ → ℝ}
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C modelMass)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass := by
  classical
  let eqWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hEq)
  have heqWindow_spec :
      0 < eqWindow ∧
        ∀ p, p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC →
          fkMass p = modelMass p := by
    simpa [eqWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hEq)
  exact
    { pδ := min hratio.pδ eqWindow
      pδ_pos := lt_min hratio.pδ_pos heqWindow_spec.1
      fkMass_pos := by
        intro p hp
        have hpMass :
            p ∈ Set.Ioo (Ising3DFKPC - hratio.pδ) Ising3DFKPC := by
          constructor
          · linarith [hp.1, min_le_left hratio.pδ eqWindow]
          · exact hp.2
        have hpEq :
            p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC := by
          constructor
          · linarith [hp.1, min_le_right hratio.pδ eqWindow]
          · exact hp.2
        have hlocal : fkMass p = modelMass p :=
          heqWindow_spec.2 p hpEq
        rw [hlocal]
        exact hratio.fkMass_pos p hpMass
      log_fk_mass_ratio_tendsto := by
        refine Filter.Tendsto.congr' ?_ hratio.log_fk_mass_ratio_tendsto
        filter_upwards [hEq] with p hlocal
        simp [hlocal] }

namespace FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical D fkMass where
  pδ := h.pδ
  pδ_pos := h.pδ_pos
  fkMass_pos := h.fkMass_pos
  log_fk_mass_ratio_sandwich := by
    intro ε hε
    filter_upwards [h.log_fk_mass_ratio_sandwich ε hε] with p hp
    simpa [hpred] using hp

end FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogRatioSandwich_of_eventuallyEq
    (C : RGCertificate Ising3DModel)
    {fkMass modelMass : ℝ → ℝ}
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C modelMass)
    (hEq :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        fkMass p = modelMass p) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass := by
  classical
  let eqWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hEq)
  have heqWindow_spec :
      0 < eqWindow ∧
        ∀ p, p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC →
          fkMass p = modelMass p := by
    simpa [eqWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hEq)
  exact
    { pδ := min hsand.pδ eqWindow
      pδ_pos := lt_min hsand.pδ_pos heqWindow_spec.1
      fkMass_pos := by
        intro p hp
        have hpMass :
            p ∈ Set.Ioo (Ising3DFKPC - hsand.pδ) Ising3DFKPC := by
          constructor
          · linarith [hp.1, min_le_left hsand.pδ eqWindow]
          · exact hp.2
        have hpEq :
            p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC := by
          constructor
          · linarith [hp.1, min_le_right hsand.pδ eqWindow]
          · exact hp.2
        have hlocal : fkMass p = modelMass p :=
          heqWindow_spec.2 p hpEq
        rw [hlocal]
        exact hsand.fkMass_pos p hpMass
      log_fk_mass_ratio_sandwich := by
        intro ε hε
        filter_upwards [hsand.log_fk_mass_ratio_sandwich ε hε, hEq]
          with p hp hlocal
        constructor
        · simpa [hlocal] using hp.1
        · simpa [hlocal] using hp.2 }

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass where
  pδ := hsand.pδ
  pδ_pos := hsand.pδ_pos
  fkMass_pos := hsand.fkMass_pos
  log_fk_mass_ratio_tendsto := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hsand.log_fk_mass_ratio_sandwich ε hε] with p hp
    rw [Real.dist_eq]
    exact abs_sub_lt_iff.mpr (by constructor <;> linarith [hp.1, hp.2])

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogRatioSandwich_of_logRatioLimit
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass where
  pδ := hratio.pδ
  pδ_pos := hratio.pδ_pos
  fkMass_pos := hratio.fkMass_pos
  log_fk_mass_ratio_sandwich := by
    intro ε hε
    have hdist :=
      (Metric.tendsto_nhds.mp hratio.log_fk_mass_ratio_tendsto) ε hε
    filter_upwards [hdist] with p hp
    rw [Real.dist_eq] at hp
    have hpabs := abs_sub_lt_iff.mp hp
    constructor <;> linarith [hpabs.1, hpabs.2]

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_logRatioLimit
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass where
  pδ := hratio.pδ
  pδ_pos := hratio.pδ_pos
  logRemainder := fun p =>
    Real.log (fkMass p) -
      C.predictedExponent * Real.log (Ising3DFKPC - p)
  fkMass_pos := hratio.fkMass_pos
  logRemainder_negligible := by
    let L := nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC)
    have hconst :
        Filter.Tendsto (fun _ : ℝ => C.predictedExponent) L
          (nhds C.predictedExponent) :=
      tendsto_const_nhds
    have hshift :
        Filter.Tendsto
          (fun p : ℝ =>
            Real.log (fkMass p) / Real.log (Ising3DFKPC - p) -
              C.predictedExponent)
          L (nhds 0) := by
      simpa [L] using hratio.log_fk_mass_ratio_tendsto.sub hconst
    refine Filter.Tendsto.congr' ?_ hshift
    filter_upwards
      [Ioo_mem_nhdsLT
        (show Ising3DFKPC - 1 < Ising3DFKPC by linarith)] with p hp
    have hdiff : Ising3DFKPC - p ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hp.1, hp.2]
    have hden : Real.log (Ising3DFKPC - p) ≠ 0 :=
      (Real.log_neg hdiff.1 hdiff.2).ne
    change
      Real.log (fkMass p) / Real.log (Ising3DFKPC - p) -
          C.predictedExponent =
        (Real.log (fkMass p) -
            C.predictedExponent * Real.log (Ising3DFKPC - p)) /
          Real.log (Ising3DFKPC - p)
    field_simp [hden]
  log_fk_mass_scaling := by
    intro p hp
    ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_logAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hlog :
      FreePositiveSubcriticalMassFKPCLogAffineNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass where
  pδ := hlog.pδ
  pδ_pos := hlog.pδ_pos
  massPrefactor := fun p => Real.exp (hlog.logRemainder p)
  massPrefactor_pos := by
    intro p hp
    exact Real.exp_pos _
  massPrefactor_log_negligible := by
    simpa [Real.log_exp] using hlog.logRemainder_negligible
  mass_scaling := by
    intro p hp
    have hmpos : 0 < fkMass p := hlog.fkMass_pos p hp
    calc
      fkMass p =
          Real.exp (Real.log (fkMass p)) := by
        rw [Real.exp_log hmpos]
      _ =
          Real.exp
            (C.predictedExponent * Real.log (Ising3DFKPC - p) +
              hlog.logRemainder p) := by
        rw [hlog.log_fk_mass_scaling p hp]
      _ =
          Real.exp (hlog.logRemainder p) *
            Real.exp (C.predictedExponent * Real.log (Ising3DFKPC - p)) := by
        rw [Real.exp_add, mul_comm]

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioLimit
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCExactPowerLaw_of_logAffineNearCritical
    C fkMass
    (freePositiveSubcriticalMassFKPCLogAffineNearCritical_of_logRatioLimit
      C fkMass hratio)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hsand :
      FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass :=
  freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioLimit
    C fkMass
    (freePositiveSubcriticalMassFKPCLogRatioLimit_of_logRatioSandwich
      C fkMass hsand)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget
    (C : RGCertificate Ising3DModel)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C T.fkMass where
  pδ := T.pδ
  pδ_pos := T.pδ_pos
  massPrefactor := T.fkMassPrefactor
  massPrefactor_pos := by
    intro p hp
    exact T.fkMassPrefactor_pos p (by
      simpa [Ising3DFKPC, ← hβeq] using hp)
  massPrefactor_log_negligible := by
    simpa [Ising3DFKPC, ← hβeq] using T.fkMassPrefactor_log_negligible
  mass_scaling := by
    intro p hp
    simpa [Ising3DFKPC, ← hβeq] using
      T.fk_mass_scaling p (by
        simpa [Ising3DFKPC, ← hβeq] using hp)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget_eq
    (C : RGCertificate Ising3DModel)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    {fkMass : ℝ → ℝ}
    (hfkMass : T.fkMass = fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass := by
  subst fkMass
  exact freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget
    C hβeq T

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCExactPowerLaw_of_fkMassPowerLawTarget_eventuallyEq
    (C : RGCertificate Ising3DModel)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    {fkMass : ℝ → ℝ}
    (hfkMass :
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        T.fkMass p = fkMass p) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass where
  pδ :=
    min T.pδ
      (Classical.choose
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hfkMass))
  pδ_pos := by
    exact lt_min T.pδ_pos
      (Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hfkMass)).1
  massPrefactor := T.fkMassPrefactor
  massPrefactor_pos := by
    intro p hp
    have hpT : p ∈ Set.Ioo (Ising3DFKPC - T.pδ) Ising3DFKPC := by
      constructor
      · linarith [hp.1, min_le_left T.pδ
          (Classical.choose
            (FKReparameterization.exists_Ioo_subset_of_eventually_left
              hfkMass))]
      · exact hp.2
    exact T.fkMassPrefactor_pos p (by
      simpa [Ising3DFKPC, ← hβeq] using hpT)
  massPrefactor_log_negligible := by
    simpa [Ising3DFKPC, ← hβeq] using T.fkMassPrefactor_log_negligible
  mass_scaling := by
    intro p hp
    let eqWindow : ℝ :=
      Classical.choose
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hfkMass)
    have heqWindow_spec :
        0 < eqWindow ∧
          ∀ p, p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC →
            T.fkMass p = fkMass p := by
      simpa [eqWindow] using
        Classical.choose_spec
          (FKReparameterization.exists_Ioo_subset_of_eventually_left hfkMass)
    have hpT : p ∈ Set.Ioo (Ising3DFKPC - T.pδ) Ising3DFKPC := by
      constructor
      · linarith [hp.1, min_le_left T.pδ eqWindow]
      · exact hp.2
    have hpEq : p ∈ Set.Ioo (Ising3DFKPC - eqWindow) Ising3DFKPC := by
      constructor
      · linarith [hp.1, min_le_right T.pδ eqWindow]
      · exact hp.2
    have hlocal : T.fkMass p = fkMass p :=
      heqWindow_spec.2 p hpEq
    have hscale :
        T.fkMass p =
          T.fkMassPrefactor p *
            Real.exp (C.predictedExponent * Real.log (Ising3DFKPC - p)) := by
      simpa [Ising3DFKPC, ← hβeq] using
        T.fk_mass_scaling p (by
          simpa [Ising3DFKPC, ← hβeq] using hpT)
    exact hlocal.symm.trans hscale

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_eventuallyLengthEq
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β) :
    FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass := by
  classical
  let pWindow : ℝ → ℝ := fun _ => T.pδ
  have hpWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε := by
    intro _ _
    exact T.pδ_pos
  have hfkLength_event :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        T.isingCorrelationLength β =
          T.fkCorrelationLength (IsingFK.pOfBeta β) := by
    simpa [Ising3DFKBetaC, ← hβeq] using T.ising_fk_length_agree
  let fkLengthWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left
        hfkLength_event)
  have hfkLengthWindow_spec :
      0 < fkLengthWindow ∧
        ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - fkLengthWindow) Ising3DFKBetaC →
          T.isingCorrelationLength β =
            T.fkCorrelationLength (IsingFK.pOfBeta β) := by
    simpa [fkLengthWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left
          hfkLength_event)
  let selectedLengthWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left
        hisingLength)
  have hselectedLengthWindow_spec :
      0 < selectedLengthWindow ∧
        ∀ β,
          β ∈ Set.Ioo (Ising3DFKBetaC - selectedLengthWindow) Ising3DFKBetaC →
            T.isingCorrelationLength β =
              freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β := by
    simpa [selectedLengthWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left
          hisingLength)
  refine
    { fkMass := T.fkMass
      selectedWindow := fun ε =>
        min (min fkLengthWindow selectedLengthWindow)
          (FKReparameterization.pOfBetaLeftPullbackWindow
            Ising3DFKBetaC pWindow hpWindow_pos ε)
      selectedWindow_pos := ?_
      selected_mass_eq_fkMass := ?_ }
  · intro ε hε
    exact lt_min (lt_min hfkLengthWindow_spec.1 hselectedLengthWindow_spec.1)
      (FKReparameterization.pOfBetaLeftPullbackWindow_pos
        Ising3DFKBetaC pWindow hpWindow_pos hε)
  · intro ε hε β hβ
    have hfkLength_le :
        min (min fkLengthWindow selectedLengthWindow)
            (FKReparameterization.pOfBetaLeftPullbackWindow
              Ising3DFKBetaC pWindow hpWindow_pos ε) ≤
          fkLengthWindow :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hselectedLength_le :
        min (min fkLengthWindow selectedLengthWindow)
            (FKReparameterization.pOfBetaLeftPullbackWindow
              Ising3DFKBetaC pWindow hpWindow_pos ε) ≤
          selectedLengthWindow :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hpull_le :
        min (min fkLengthWindow selectedLengthWindow)
            (FKReparameterization.pOfBetaLeftPullbackWindow
              Ising3DFKBetaC pWindow hpWindow_pos ε) ≤
          FKReparameterization.pOfBetaLeftPullbackWindow
            Ising3DFKBetaC pWindow hpWindow_pos ε :=
      min_le_right _ _
    have hβ_fkLength :
        β ∈ Set.Ioo (Ising3DFKBetaC - fkLengthWindow) Ising3DFKBetaC := by
      constructor
      · linarith [hβ.1, hfkLength_le]
      · exact hβ.2
    have hβ_selectedLength :
        β ∈ Set.Ioo (Ising3DFKBetaC - selectedLengthWindow)
          Ising3DFKBetaC := by
      constructor
      · linarith [hβ.1, hselectedLength_le]
      · exact hβ.2
    have hβ_pullback :
        β ∈ Set.Ioo
          (Ising3DFKBetaC -
            FKReparameterization.pOfBetaLeftPullbackWindow
              Ising3DFKBetaC pWindow hpWindow_pos ε)
          Ising3DFKBetaC := by
      constructor
      · linarith [hβ.1, hpull_le]
      · exact hβ.2
    have hpwin :
        IsingFK.pOfBeta β ∈ Set.Ioo (Ising3DFKPC - T.pδ)
          Ising3DFKPC := by
      simpa [pWindow, Ising3DFKPC] using
        FKReparameterization.pOfBeta_mem_Ioo_of_mem_leftPullbackWindow
          Ising3DFKBetaC pWindow hpWindow_pos hε hβ_pullback
    have hfkAgree :=
      hfkLengthWindow_spec.2 β hβ_fkLength
    have hselectedAgree :=
      hselectedLengthWindow_spec.2 β hβ_selectedLength
    have hlength :
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          T.fkCorrelationLength (IsingFK.pOfBeta β) :=
      hselectedAgree.symm.trans hfkAgree
    have hfk_length :
        T.fkCorrelationLength (IsingFK.pOfBeta β) =
          (T.fkMass (IsingFK.pOfBeta β))⁻¹ := by
      exact T.fk_length_eq_inv_mass (IsingFK.pOfBeta β) (by
        simpa [Ising3DFKPC, ← hβeq] using hpwin)
    have hinv :
        (freeSelectedPositiveSubcriticalMass hmass β)⁻¹ =
          (T.fkMass (IsingFK.pOfBeta β))⁻¹ := by
      unfold freeSelectedPositiveSubcriticalCorrelationLengthFromMass at hlength
      simpa [hfk_length] using hlength
    simpa using congrArg Inv.inv hinv

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_lengthEq
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hisingLength :
      T.isingCorrelationLength =
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass) :
    FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass :=
  freePositiveSubcriticalMassFKPCSelectedAgreement_of_fkMassPowerLawTarget_eventuallyLengthEq
    C hmass hβeq T
    (Filter.Eventually.of_forall fun β => by
      rw [hisingLength])

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLowerExists_of_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    {fkMass : ℝ → ℝ}
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
      C fkMass where
  p_mass_lower_exists := by
    intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hsmall :
        ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
          Real.log (hexact.massPrefactor p) /
              Real.log (Ising3DFKPC - p) <
            ε / 2 := by
      have hdist :=
        (Metric.tendsto_nhds.mp hexact.massPrefactor_log_negligible)
          (ε / 2) hhalf
      filter_upwards [hdist] with p hp
      rw [Real.dist_eq] at hp
      exact (abs_lt.mp (by simpa using hp)).2
    have hevent :
        ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
          (1 : ℝ) *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising3DFKPC - p)) ≤
            fkMass p := by
      filter_upwards
        [hsmall,
          Ioo_mem_nhdsLT
            (show Ising3DFKPC - hexact.pδ < Ising3DFKPC by
              linarith [hexact.pδ_pos]),
          Ioo_mem_nhdsLT
            (show Ising3DFKPC - 1 < Ising3DFKPC by norm_num)]
        with p hsmallp hpδ hpone
      let L := Real.log (Ising3DFKPC - p)
      have hdist01 : Ising3DFKPC - p ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hpone.1, hpone.2]
      have hLneg : L < 0 := by
        simpa [L] using Real.log_neg hdist01.1 hdist01.2
      have hLne : L ≠ 0 := hLneg.ne
      have hpref_pos : 0 < hexact.massPrefactor p :=
        hexact.massPrefactor_pos p hpδ
      have hlog_pref_lower :
          (ε / 2) * L < Real.log (hexact.massPrefactor p) := by
        calc
          (ε / 2) * L <
              (Real.log (hexact.massPrefactor p) / L) * L := by
            exact mul_lt_mul_of_neg_right hsmallp hLneg
          _ = Real.log (hexact.massPrefactor p) := by
            field_simp [hLne]
      have hexp_le :
          Real.exp
              ((C.predictedExponent + ε / 2) * L) ≤
            hexact.massPrefactor p *
              Real.exp (C.predictedExponent * L) := by
        calc
          Real.exp
              ((C.predictedExponent + ε / 2) * L) ≤
              Real.exp
                (Real.log (hexact.massPrefactor p) +
                  C.predictedExponent * L) := by
            rw [Real.exp_le_exp]
            linarith
          _ =
              hexact.massPrefactor p *
                Real.exp (C.predictedExponent * L) := by
            rw [Real.exp_add, Real.exp_log hpref_pos]
      calc
        (1 : ℝ) *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising3DFKPC - p)) =
          Real.exp
            ((C.predictedExponent + ε / 2) * L) := by
            simp [L]
        _ ≤
          hexact.massPrefactor p *
            Real.exp (C.predictedExponent * L) :=
            hexp_le
        _ = fkMass p := by
            rw [hexact.mass_scaling p hpδ]
    obtain ⟨δ, hδpos, hδ⟩ :=
      FKReparameterization.exists_Ioo_subset_of_eventually_left hevent
    exact ⟨(1, δ), by norm_num, hδpos, hδ⟩

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCUpperExists_of_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    {fkMass : ℝ → ℝ}
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
      C fkMass where
  p_mass_upper_exists := by
    intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hsmall :
        ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
          -(ε / 2) <
            Real.log (hexact.massPrefactor p) /
              Real.log (Ising3DFKPC - p) := by
      have hdist :=
        (Metric.tendsto_nhds.mp hexact.massPrefactor_log_negligible)
          (ε / 2) hhalf
      filter_upwards [hdist] with p hp
      rw [Real.dist_eq] at hp
      exact (abs_lt.mp (by simpa using hp)).1
    have hevent :
        ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
          fkMass p ≤
            (1 : ℝ) *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKPC - p)) := by
      filter_upwards
        [hsmall,
          Ioo_mem_nhdsLT
            (show Ising3DFKPC - hexact.pδ < Ising3DFKPC by
              linarith [hexact.pδ_pos]),
          Ioo_mem_nhdsLT
            (show Ising3DFKPC - 1 < Ising3DFKPC by norm_num)]
        with p hsmallp hpδ hpone
      let L := Real.log (Ising3DFKPC - p)
      have hdist01 : Ising3DFKPC - p ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hpone.1, hpone.2]
      have hLneg : L < 0 := by
        simpa [L] using Real.log_neg hdist01.1 hdist01.2
      have hLne : L ≠ 0 := hLneg.ne
      have hpref_pos : 0 < hexact.massPrefactor p :=
        hexact.massPrefactor_pos p hpδ
      have hlog_pref_upper :
          Real.log (hexact.massPrefactor p) < -(ε / 2) * L := by
        calc
          Real.log (hexact.massPrefactor p) =
              (Real.log (hexact.massPrefactor p) / L) * L := by
            field_simp [hLne]
          _ < -(ε / 2) * L := by
            exact mul_lt_mul_of_neg_right hsmallp hLneg
      have hexp_le :
          hexact.massPrefactor p *
              Real.exp (C.predictedExponent * L) ≤
            Real.exp
              ((C.predictedExponent - ε / 2) * L) := by
        calc
          hexact.massPrefactor p *
              Real.exp (C.predictedExponent * L) =
              Real.exp
                (Real.log (hexact.massPrefactor p) +
                  C.predictedExponent * L) := by
            rw [Real.exp_add, Real.exp_log hpref_pos]
          _ ≤
              Real.exp
                ((C.predictedExponent - ε / 2) * L) := by
            rw [Real.exp_le_exp]
            linarith
      calc
        fkMass p =
          hexact.massPrefactor p *
            Real.exp (C.predictedExponent * L) := by
            rw [hexact.mass_scaling p hpδ]
        _ ≤
          Real.exp
            ((C.predictedExponent - ε / 2) * L) :=
            hexp_le
        _ =
          (1 : ℝ) *
            Real.exp
              ((C.predictedExponent - ε / 2) *
                Real.log (Ising3DFKPC - p)) := by
            simp [L]
    obtain ⟨δ, hδpos, hδ⟩ :=
      FKReparameterization.exists_Ioo_subset_of_eventually_left hevent
    exact ⟨(1, δ), by norm_num, hδpos, hδ⟩

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCLower_of_exists
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
      C fkMass where
  lowerPrefactor := fun ε =>
    if hε : 0 < ε then
      (Classical.choose (hlower.p_mass_lower_exists ε hε)).1
    else 1
  pWindow := fun ε =>
    if hε : 0 < ε then
      (Classical.choose (hlower.p_mass_lower_exists ε hε)).2
    else 1
  lowerPrefactor_pos := by
    intro ε hε
    rw [dif_pos hε]
    exact (Classical.choose_spec (hlower.p_mass_lower_exists ε hε)).1
  pWindow_pos := by
    intro ε hε
    rw [dif_pos hε]
    exact (Classical.choose_spec (hlower.p_mass_lower_exists ε hε)).2.1
  p_mass_lower_on_Ioo := by
    intro ε hε q hq
    have hq' :
        q ∈ Set.Ioo
          (Ising3DFKPC -
            (Classical.choose (hlower.p_mass_lower_exists ε hε)).2)
          Ising3DFKPC := by
      simpa [dif_pos hε] using hq
    simpa [dif_pos hε] using
      (Classical.choose_spec (hlower.p_mass_lower_exists ε hε)).2.2 q hq'

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCUpper_of_exists
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
      C fkMass where
  upperPrefactor := fun ε =>
    if hε : 0 < ε then
      (Classical.choose (hupper.p_mass_upper_exists ε hε)).1
    else 1
  pWindow := fun ε =>
    if hε : 0 < ε then
      (Classical.choose (hupper.p_mass_upper_exists ε hε)).2
    else 1
  upperPrefactor_pos := by
    intro ε hε
    rw [dif_pos hε]
    exact (Classical.choose_spec (hupper.p_mass_upper_exists ε hε)).1
  pWindow_pos := by
    intro ε hε
    rw [dif_pos hε]
    exact (Classical.choose_spec (hupper.p_mass_upper_exists ε hε)).2.1
  p_mass_upper_on_Ioo := by
    intro ε hε q hq
    have hq' :
        q ∈ Set.Ioo
          (Ising3DFKPC -
            (Classical.choose (hupper.p_mass_upper_exists ε hε)).2)
          Ising3DFKPC := by
      simpa [dif_pos hε] using hq
    simpa [dif_pos hε] using
      (Classical.choose_spec (hupper.p_mass_upper_exists ε hε)).2.2 q hq'

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lower_upper
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C hselected.fkMass) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass where
  fkMass := hselected.fkMass
  lowerPrefactor := hlower.lowerPrefactor
  upperPrefactor := hupper.upperPrefactor
  pWindow := fun ε => min (hlower.pWindow ε) (hupper.pWindow ε)
  selectedWindow := hselected.selectedWindow
  lowerPrefactor_pos := hlower.lowerPrefactor_pos
  upperPrefactor_pos := hupper.upperPrefactor_pos
  pWindow_pos := by
    intro ε hε
    exact lt_min (hlower.pWindow_pos ε hε) (hupper.pWindow_pos ε hε)
  selectedWindow_pos := hselected.selectedWindow_pos
  selected_mass_eq_fkMass := hselected.selected_mass_eq_fkMass
  p_mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε p hp
    have hp_lower :
        p ∈ Set.Ioo (Ising3DFKPC - hlower.pWindow ε) Ising3DFKPC := by
      constructor
      · have hle :
            Ising3DFKPC - hlower.pWindow ε ≤
              Ising3DFKPC - min (hlower.pWindow ε) (hupper.pWindow ε) :=
          sub_le_sub_left
            (min_le_left (hlower.pWindow ε) (hupper.pWindow ε))
            Ising3DFKPC
        exact lt_of_le_of_lt hle hp.1
      · exact hp.2
    have hp_upper :
        p ∈ Set.Ioo (Ising3DFKPC - hupper.pWindow ε) Ising3DFKPC := by
      constructor
      · have hle :
            Ising3DFKPC - hupper.pWindow ε ≤
              Ising3DFKPC - min (hlower.pWindow ε) (hupper.pWindow ε) :=
          sub_le_sub_left
            (min_le_right (hlower.pWindow ε) (hupper.pWindow ε))
            Ising3DFKPC
        exact lt_of_le_of_lt hle hp.1
      · exact hp.2
    constructor
    · exact hlower.p_mass_lower_on_Ioo ε hε p hp_lower
    · exact hupper.p_mass_upper_on_Ioo ε hε p hp_upper

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lowerUpperExists
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C hselected.fkMass) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lower_upper
    C hmass hselected
    (freePositiveSubcriticalMassFKPCLower_of_exists C hselected.fkMass hlower)
    (freePositiveSubcriticalMassFKPCUpper_of_exists C hselected.fkMass hupper)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_exactPowerLaw
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lowerUpperExists
    C hmass hselected
    (freePositiveSubcriticalMassFKPCLowerExists_of_exactPowerLaw C hexact)
    (freePositiveSubcriticalMassFKPCUpperExists_of_exactPowerLaw C hexact)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCSelectedIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
      C hmass where
  lowerPrefactor := fun ε =>
    hp.lowerPrefactor ε *
      Real.exp
        ((C.predictedExponent + ε / 2) *
          Real.log (Real.exp (-2 * Ising3DFKBetaC)))
  upperPrefactor := fun ε =>
    hp.upperPrefactor ε *
      FKReparameterization.expLogUpperComparisonPrefactor
        (Real.exp (-2 * Ising3DFKBetaC))
        (3 * Real.exp (-2 * Ising3DFKBetaC))
        (C.predictedExponent - ε / 2)
  window := fun ε =>
    min
      (min
        (hp.selectedWindow ε)
        (FKReparameterization.pOfBetaLeftPullbackWindow
          Ising3DFKBetaC hp.pWindow hp.pWindow_pos ε))
      (FKReparameterization.pOfBetaCriticalDistanceComparableWindow
        Ising3DFKBetaC)
  lowerPrefactor_pos := by
    intro ε hε
    exact mul_pos (hp.lowerPrefactor_pos ε hε) (Real.exp_pos _)
  upperPrefactor_pos := by
    intro ε hε
    exact mul_pos (hp.upperPrefactor_pos ε hε)
      (FKReparameterization.expLogUpperComparisonPrefactor_pos _ _ _)
  window_pos := by
    intro ε hε
    exact lt_min
      (lt_min (hp.selectedWindow_pos ε hε)
        (FKReparameterization.pOfBetaLeftPullbackWindow_pos
          Ising3DFKBetaC hp.pWindow hp.pWindow_pos hε))
      (FKReparameterization.pOfBetaCriticalDistanceComparableWindow_pos
        Ising3DFKBetaC)
  mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε β hβ
    let lo : ℝ := Real.exp (-2 * Ising3DFKBetaC)
    let hi : ℝ := 3 * Real.exp (-2 * Ising3DFKBetaC)
    let d : ℝ := Ising3DFKBetaC - β
    let pd : ℝ := Ising3DFKPC - IsingFK.pOfBeta β
    have hlo : 0 < lo := by
      dsimp [lo]
      exact Real.exp_pos _
    have hhi : 0 < hi := by
      dsimp [hi]
      exact mul_pos (by norm_num) (Real.exp_pos _)
    have hd : 0 < d := by
      dsimp [d]
      exact sub_pos.mpr hβ.2
    have hwin_selected :
        min
            (min
              (hp.selectedWindow ε)
              (FKReparameterization.pOfBetaLeftPullbackWindow
                Ising3DFKBetaC hp.pWindow hp.pWindow_pos ε))
            (FKReparameterization.pOfBetaCriticalDistanceComparableWindow
              Ising3DFKBetaC) ≤
          hp.selectedWindow ε :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hwin_pullback :
        min
            (min
              (hp.selectedWindow ε)
              (FKReparameterization.pOfBetaLeftPullbackWindow
                Ising3DFKBetaC hp.pWindow hp.pWindow_pos ε))
            (FKReparameterization.pOfBetaCriticalDistanceComparableWindow
              Ising3DFKBetaC) ≤
          FKReparameterization.pOfBetaLeftPullbackWindow
            Ising3DFKBetaC hp.pWindow hp.pWindow_pos ε :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hwin_compare :
        min
            (min
              (hp.selectedWindow ε)
              (FKReparameterization.pOfBetaLeftPullbackWindow
                Ising3DFKBetaC hp.pWindow hp.pWindow_pos ε))
            (FKReparameterization.pOfBetaCriticalDistanceComparableWindow
              Ising3DFKBetaC) ≤
          FKReparameterization.pOfBetaCriticalDistanceComparableWindow
            Ising3DFKBetaC :=
      min_le_right _ _
    have hβ_selected :
        β ∈ Set.Ioo (Ising3DFKBetaC - hp.selectedWindow ε)
          Ising3DFKBetaC := by
      constructor
      · linarith [hβ.1, hwin_selected]
      · exact hβ.2
    have hβ_pullback :
        β ∈ Set.Ioo
          (Ising3DFKBetaC -
            FKReparameterization.pOfBetaLeftPullbackWindow
              Ising3DFKBetaC hp.pWindow hp.pWindow_pos ε)
          Ising3DFKBetaC := by
      constructor
      · linarith [hβ.1, hwin_pullback]
      · exact hβ.2
    have hβ_compare :
        β ∈ Set.Ioo
          (Ising3DFKBetaC -
            FKReparameterization.pOfBetaCriticalDistanceComparableWindow
              Ising3DFKBetaC)
          Ising3DFKBetaC := by
      constructor
      · linarith [hβ.1, hwin_compare]
      · exact hβ.2
    have hpwin :
        IsingFK.pOfBeta β ∈ Set.Ioo (Ising3DFKPC - hp.pWindow ε)
          Ising3DFKPC := by
      simpa [Ising3DFKPC] using
        FKReparameterization.pOfBeta_mem_Ioo_of_mem_leftPullbackWindow
          Ising3DFKBetaC hp.pWindow hp.pWindow_pos hε hβ_pullback
    have hcmp_raw :=
      FKReparameterization.pOfBeta_criticalDistance_comparable_of_mem_Ioo_left
        hβ_compare
    have hcmp :
        lo * d ≤ pd ∧ pd ≤ hi * d := by
      simpa [lo, hi, d, pd, Ising3DFKPC] using hcmp_raw
    have hsel := hp.selected_mass_eq_fkMass ε hε β hβ_selected
    have hpsand :=
      hp.p_mass_constant_prefactor_power_sandwich_on_Ioo
        ε hε (IsingFK.pOfBeta β) hpwin
    rw [hsel]
    constructor
    · have hk :
          0 ≤ C.predictedExponent + ε / 2 := by
        exact le_of_lt (add_pos (C.predictedExponent_pos) (half_pos hε))
      have htransfer :
          Real.exp ((C.predictedExponent + ε / 2) * Real.log lo) *
              Real.exp ((C.predictedExponent + ε / 2) * Real.log d) ≤
            Real.exp ((C.predictedExponent + ε / 2) * Real.log pd) :=
        FKReparameterization.exp_log_lower_power_transfer_no_slack_of_mul_le
          hlo hd hk hcmp.1
      calc
        (hp.lowerPrefactor ε *
              Real.exp
                ((C.predictedExponent + ε / 2) * Real.log lo)) *
            Real.exp ((C.predictedExponent + ε / 2) * Real.log d)
            =
          hp.lowerPrefactor ε *
            (Real.exp
                ((C.predictedExponent + ε / 2) * Real.log lo) *
              Real.exp ((C.predictedExponent + ε / 2) * Real.log d)) := by
            ring
        _ ≤
          hp.lowerPrefactor ε *
            Real.exp ((C.predictedExponent + ε / 2) * Real.log pd) := by
            exact mul_le_mul_of_nonneg_left htransfer
              (le_of_lt (hp.lowerPrefactor_pos ε hε))
        _ ≤ hp.fkMass (IsingFK.pOfBeta β) := by
            simpa [pd] using hpsand.1
    · have htransfer :
          Real.exp ((C.predictedExponent - ε / 2) * Real.log pd) ≤
            FKReparameterization.expLogUpperComparisonPrefactor lo hi
                (C.predictedExponent - ε / 2) *
              Real.exp ((C.predictedExponent - ε / 2) * Real.log d) :=
        FKReparameterization.exp_log_upper_power_transfer_of_comparable
          hlo hhi hd hcmp.1 hcmp.2
      calc
        hp.fkMass (IsingFK.pOfBeta β) ≤
          hp.upperPrefactor ε *
            Real.exp ((C.predictedExponent - ε / 2) * Real.log pd) := by
            simpa [pd] using hpsand.2
        _ ≤
          hp.upperPrefactor ε *
            (FKReparameterization.expLogUpperComparisonPrefactor lo hi
                (C.predictedExponent - ε / 2) *
              Real.exp ((C.predictedExponent - ε / 2) * Real.log d)) := by
            exact mul_le_mul_of_nonneg_left htransfer
              (le_of_lt (hp.upperPrefactor_pos ε hε))
        _ =
          (hp.upperPrefactor ε *
              FKReparameterization.expLogUpperComparisonPrefactor lo hi
                (C.predictedExponent - ε / 2)) *
            Real.exp ((C.predictedExponent - ε / 2) * Real.log d) := by
            ring

set_option linter.style.longLine false in


def freePositiveSubcriticalMassFKBetaCLowerBoundExistsNoWindow_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
      C hmass where
  mass_lower_exists := by
    intro ε hε
    refine ⟨(hsand.lowerPrefactor ε, hsand.window ε), ?_, ?_, ?_⟩
    · exact hsand.lowerPrefactor_pos ε hε
    · exact hsand.window_pos ε hε
    · intro β hβ
      exact (hsand.mass_constant_prefactor_power_sandwich_on_Ioo ε hε β hβ).1

set_option linter.style.longLine false in


def freePositiveSubcriticalMassFKBetaCUpperExists_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical
      C hmass where
  mass_upper_exists := by
    intro ε hε
    refine ⟨(hsand.upperPrefactor ε, hsand.window ε), ?_, ?_, ?_⟩
    · exact hsand.upperPrefactor_pos ε hε
    · exact hsand.window_pos ε hε
    · intro β hβ
      exact (hsand.mass_constant_prefactor_power_sandwich_on_Ioo ε hε β hβ).2

set_option linter.style.longLine false in


def freePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindow_of_fkBetaC
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hlower :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
      C hmass where
  mass_lower_exists := by
    intro ε hε
    obtain ⟨p, hp_pref, hp_window, hp_bound⟩ := hlower.mass_lower_exists ε hε
    refine ⟨p, hp_pref, hp_window, ?_⟩
    intro β hβ
    have hβ_fk : β ∈ Set.Ioo (Ising3DFKBetaC - p.2) Ising3DFKBetaC := by
      simpa [Ising3DFKBetaC, ← hβeq] using hβ
    simpa [Ising3DFKBetaC, ← hβeq] using hp_bound β hβ_fk

set_option linter.style.longLine false in


def freePositiveSubcriticalMassConstantPrefactorWeakIooUpperExists_of_fkBetaC
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hupper :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
      C hmass where
  mass_upper_exists := by
    intro ε hε
    obtain ⟨p, hp_pref, hp_window, hp_bound⟩ := hupper.mass_upper_exists ε hε
    refine ⟨p, hp_pref, hp_window, ?_⟩
    intro β hβ
    have hβ_fk : β ∈ Set.Ioo (Ising3DFKBetaC - p.2) Ising3DFKBetaC := by
      simpa [Ising3DFKBetaC, ← hβeq] using hβ
    simpa [Ising3DFKBetaC, ← hβeq] using hp_bound β hβ_fk

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassConstantPrefactorWeakIooSandwich_of_fkBetaCIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
      C hmass where
  δ := min (hsand.window 1) (Ising.betaC 3)
  δ_pos := lt_min (hsand.window_pos 1 zero_lt_one) hβc
  δ_le_betaC := min_le_right _ _
  lowerPrefactor := hsand.lowerPrefactor
  upperPrefactor := hsand.upperPrefactor
  window := hsand.window
  mass_pos := by
    intro β hβ
    have hβ_window :
        β ∈ Set.Ioo (Ising.betaC 3 - hsand.window 1) (Ising.betaC 3) := by
      constructor
      · linarith [hβ.1, min_le_left (hsand.window 1) (Ising.betaC 3)]
      · exact hβ.2
    have hβ_fk :
        β ∈ Set.Ioo (Ising3DFKBetaC - hsand.window 1) Ising3DFKBetaC := by
      simpa [Ising3DFKBetaC, ← hβeq] using hβ_window
    have hlower :=
      (hsand.mass_constant_prefactor_power_sandwich_on_Ioo
        1 zero_lt_one β hβ_fk).1
    have hprod_pos :
        0 <
          hsand.lowerPrefactor 1 *
            Real.exp
              ((C.predictedExponent + 1 / 2) *
                Real.log (Ising3DFKBetaC - β)) :=
      mul_pos (hsand.lowerPrefactor_pos 1 zero_lt_one) (Real.exp_pos _)
    exact lt_of_lt_of_le hprod_pos hlower
  lowerPrefactor_pos := hsand.lowerPrefactor_pos
  upperPrefactor_pos := hsand.upperPrefactor_pos
  window_pos := hsand.window_pos
  mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε β hβ
    have hβ_fk :
        β ∈ Set.Ioo (Ising3DFKBetaC - hsand.window ε) Ising3DFKBetaC := by
      simpa [Ising3DFKBetaC, ← hβeq] using hβ
    simpa [Ising3DFKBetaC, ← hβeq] using
      hsand.mass_constant_prefactor_power_sandwich_on_Ioo ε hε β hβ_fk

set_option linter.style.longLine false in


noncomputable def
    freePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExists_of_betaC_pos_noWindow
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
      C hmass where
  δ :=
    min (Ising.betaC 3)
      (Classical.choose
        (hlower.mass_lower_exists 1 (zero_lt_one : (0 : ℝ) < 1))).2
  δ_pos := by
    classical
    exact
      lt_min hβc
        (Classical.choose_spec
          (hlower.mass_lower_exists 1 (zero_lt_one : (0 : ℝ) < 1))).2.1
  δ_le_betaC := by
    exact min_le_left _ _
  mass_lower_exists := hlower.mass_lower_exists

set_option linter.style.longLine false in


noncomputable def
    freePositiveSubcriticalMassConstantPrefactorWeakIooLowerExists_of_lowerBoundExists
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
      C hmass where
  δ :=
    min hlower.δ
      (Classical.choose
        (hlower.mass_lower_exists 1 (zero_lt_one : (0 : ℝ) < 1))).2
  δ_pos := by
    classical
    exact
      lt_min hlower.δ_pos
        (Classical.choose_spec
          (hlower.mass_lower_exists 1 (zero_lt_one : (0 : ℝ) < 1))).2.1
  δ_le_betaC := by
    exact le_trans (min_le_left _ _) hlower.δ_le_betaC
  mass_pos := by
    intro β hβ
    classical
    let p :=
      Classical.choose
        (hlower.mass_lower_exists 1 (zero_lt_one : (0 : ℝ) < 1))
    have hp :
        0 < p.1 ∧ 0 < p.2 ∧
          ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - p.2) (Ising.betaC 3) →
            p.1 *
                Real.exp
                  ((C.predictedExponent + (1 : ℝ) / 2) *
                    Real.log (Ising.betaC 3 - β)) ≤
              freeSelectedPositiveSubcriticalMass hmass β := by
      simpa [p] using
        Classical.choose_spec
          (hlower.mass_lower_exists 1 (zero_lt_one : (0 : ℝ) < 1))
    change
      β ∈ Set.Ioo (Ising.betaC 3 - min hlower.δ p.2)
        (Ising.betaC 3) at hβ
    have hmin : min hlower.δ p.2 ≤ p.2 := min_le_right _ _
    have hβp : β ∈ Set.Ioo (Ising.betaC 3 - p.2) (Ising.betaC 3) := by
      constructor
      · linarith [hβ.1, hmin]
      · exact hβ.2
    have hle := hp.2.2 β hβp
    have hleft_pos :
        0 <
          p.1 *
            Real.exp
              ((C.predictedExponent + (1 : ℝ) / 2) *
                Real.log (Ising.betaC 3 - β)) := by
      exact mul_pos hp.1 (Real.exp_pos _)
    exact lt_of_lt_of_le hleft_pos hle
  mass_lower_exists := hlower.mass_lower_exists

set_option linter.style.longLine false in


noncomputable def
    freePositiveSubcriticalMassConstantPrefactorWeakIooLower_of_exists
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
      C hmass where
  δ := hlower.δ
  δ_pos := hlower.δ_pos
  δ_le_betaC := hlower.δ_le_betaC
  lowerPrefactor := fun ε => by
    classical
    exact
      (if hε : 0 < ε then
        Classical.choose (hlower.mass_lower_exists ε hε)
      else
        (1, 1)).1
  lowerWindow := fun ε => by
    classical
    exact
      (if hε : 0 < ε then
        Classical.choose (hlower.mass_lower_exists ε hε)
      else
        (1, 1)).2
  mass_pos := hlower.mass_pos
  lowerPrefactor_pos := by
    intro ε hε
    classical
    rw [dif_pos hε]
    exact (Classical.choose_spec (hlower.mass_lower_exists ε hε)).1
  lowerWindow_pos := by
    intro ε hε
    classical
    rw [dif_pos hε]
    exact (Classical.choose_spec (hlower.mass_lower_exists ε hε)).2.1
  mass_lower_on_Ioo := by
    intro ε hε β hβ
    classical
    rw [dif_pos hε] at hβ ⊢
    exact (Classical.choose_spec (hlower.mass_lower_exists ε hε)).2.2 β hβ

set_option linter.style.longLine false in


noncomputable def
    freePositiveSubcriticalMassConstantPrefactorWeakIooUpper_of_exists
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
      C hmass where
  upperPrefactor := fun ε => by
    classical
    exact
      (if hε : 0 < ε then
        Classical.choose (hupper.mass_upper_exists ε hε)
      else
        (1, 1)).1
  upperWindow := fun ε => by
    classical
    exact
      (if hε : 0 < ε then
        Classical.choose (hupper.mass_upper_exists ε hε)
      else
        (1, 1)).2
  upperPrefactor_pos := by
    intro ε hε
    classical
    rw [dif_pos hε]
    exact (Classical.choose_spec (hupper.mass_upper_exists ε hε)).1
  upperWindow_pos := by
    intro ε hε
    classical
    rw [dif_pos hε]
    exact (Classical.choose_spec (hupper.mass_upper_exists ε hε)).2.1
  mass_upper_on_Ioo := by
    intro ε hε β hβ
    classical
    rw [dif_pos hε] at hβ ⊢
    exact (Classical.choose_spec (hupper.mass_upper_exists ε hε)).2.2 β hβ

set_option linter.style.longLine false in


noncomputable def
    freePositiveSubcriticalMassConstantPrefactorWeakIooSandwich_of_constantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
      C hmass where
  δ := hlower.δ
  δ_pos := hlower.δ_pos
  δ_le_betaC := hlower.δ_le_betaC
  lowerPrefactor := hlower.lowerPrefactor
  upperPrefactor := hupper.upperPrefactor
  window := fun ε => min (hlower.lowerWindow ε) (hupper.upperWindow ε)
  mass_pos := hlower.mass_pos
  lowerPrefactor_pos := hlower.lowerPrefactor_pos
  upperPrefactor_pos := hupper.upperPrefactor_pos
  window_pos := by
    intro ε hε
    exact lt_min (hlower.lowerWindow_pos ε hε) (hupper.upperWindow_pos ε hε)
  mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε β hβ
    have hmin_lower :
        min (hlower.lowerWindow ε) (hupper.upperWindow ε) ≤
          hlower.lowerWindow ε :=
      min_le_left _ _
    have hmin_upper :
        min (hlower.lowerWindow ε) (hupper.upperWindow ε) ≤
          hupper.upperWindow ε :=
      min_le_right _ _
    have hβ_lower :
        β ∈ Set.Ioo (Ising.betaC 3 - hlower.lowerWindow ε)
          (Ising.betaC 3) := by
      constructor
      · linarith [hβ.1, hmin_lower]
      · exact hβ.2
    have hβ_upper :
        β ∈ Set.Ioo (Ising.betaC 3 - hupper.upperWindow ε)
          (Ising.betaC 3) := by
      constructor
      · linarith [hβ.1, hmin_upper]
      · exact hβ.2
    exact
      ⟨hlower.mass_lower_on_Ioo ε hε β hβ_lower,
        hupper.mass_upper_on_Ioo ε hε β hβ_upper⟩

set_option linter.style.longLine false in


noncomputable def
    freePositiveSubcriticalMassConstantPrefactorWeakSandwich_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
      C hmass where
  δ := hIoo.δ
  δ_pos := hIoo.δ_pos
  δ_le_betaC := hIoo.δ_le_betaC
  lowerPrefactor := hIoo.lowerPrefactor
  upperPrefactor := hIoo.upperPrefactor
  mass_pos := hIoo.mass_pos
  lowerPrefactor_pos := hIoo.lowerPrefactor_pos
  upperPrefactor_pos := hIoo.upperPrefactor_pos
  mass_constant_prefactor_power_sandwich := by
    intro ε hε
    have hleft : Ising.betaC 3 - hIoo.window ε < Ising.betaC 3 := by
      linarith [hIoo.window_pos ε hε]
    filter_upwards [Ioo_mem_nhdsLT hleft] with β hβ
    exact hIoo.mass_constant_prefactor_power_sandwich_on_Ioo ε hε β hβ

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassPowerSandwich_of_subpowerPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass where
  δ := hsub.δ
  δ_pos := hsub.δ_pos
  δ_le_betaC := hsub.δ_le_betaC
  mass_pos := hsub.mass_pos
  mass_power_sandwich := by
    intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hlowerSmall :
        ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
          Real.log (hsub.lowerPrefactor ε β) /
              Real.log (Ising.betaC 3 - β) <
            ε / 2 := by
      have hdist :=
        (Metric.tendsto_nhds.mp
          (hsub.lowerPrefactor_log_negligible ε hε)) (ε / 2) hhalf
      filter_upwards [hdist] with β hβ
      rw [Real.dist_eq] at hβ
      exact (abs_lt.mp (by simpa using hβ)).2
    have hupperSmall :
        ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
          -(ε / 2) <
            Real.log (hsub.upperPrefactor ε β) /
              Real.log (Ising.betaC 3 - β) := by
      have hdist :=
        (Metric.tendsto_nhds.mp
          (hsub.upperPrefactor_log_negligible ε hε)) (ε / 2) hhalf
      filter_upwards [hdist] with β hβ
      rw [Real.dist_eq] at hβ
      exact (abs_lt.mp (by simpa using hβ)).1
    filter_upwards
      [hsub.mass_prefactor_power_sandwich ε hε,
        hsub.lowerPrefactor_pos ε hε,
        hsub.upperPrefactor_pos ε hε,
        hlowerSmall,
        hupperSmall,
        Ioo_mem_nhdsLT
          (show Ising.betaC 3 - 1 < Ising.betaC 3 by linarith)]
      with β hβpref hlowerPos hupperPos hlowerSmallβ hupperSmallβ hβleft
    let m := freeSelectedPositiveSubcriticalMass hmass β
    let L := Real.log (Ising.betaC 3 - β)
    have hdist : Ising.betaC 3 - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβleft.1, hβleft.2]
    have hLneg : L < 0 := by
      simpa [L] using Real.log_neg hdist.1 hdist.2
    have hLne : L ≠ 0 := hLneg.ne
    constructor
    · have hlowerLog :
          (ε / 2) * L < Real.log (hsub.lowerPrefactor ε β) := by
        calc
          (ε / 2) * L <
              (Real.log (hsub.lowerPrefactor ε β) / L) * L := by
            exact mul_lt_mul_of_neg_right hlowerSmallβ hLneg
          _ = Real.log (hsub.lowerPrefactor ε β) := by
            field_simp [hLne]
      have hexpLower :
          Real.exp ((C.predictedExponent + ε) * L) <
            hsub.lowerPrefactor ε β *
              Real.exp ((C.predictedExponent + ε / 2) * L) := by
        calc
          Real.exp ((C.predictedExponent + ε) * L) <
              Real.exp
                (Real.log (hsub.lowerPrefactor ε β) +
                  (C.predictedExponent + ε / 2) * L) := by
            rw [Real.exp_lt_exp]
            linarith
          _ =
              hsub.lowerPrefactor ε β *
                Real.exp ((C.predictedExponent + ε / 2) * L) := by
            rw [Real.exp_add, Real.exp_log hlowerPos]
      exact lt_trans hexpLower hβpref.1
    · have hupperLog :
          Real.log (hsub.upperPrefactor ε β) < -(ε / 2) * L := by
        calc
          Real.log (hsub.upperPrefactor ε β) =
              (Real.log (hsub.upperPrefactor ε β) / L) * L := by
            field_simp [hLne]
          _ < -(ε / 2) * L := by
            exact mul_lt_mul_of_neg_right hupperSmallβ hLneg
      have hexpUpper :
          hsub.upperPrefactor ε β *
              Real.exp ((C.predictedExponent - ε / 2) * L) <
            Real.exp ((C.predictedExponent - ε) * L) := by
        calc
          hsub.upperPrefactor ε β *
              Real.exp ((C.predictedExponent - ε / 2) * L) =
              Real.exp
                (Real.log (hsub.upperPrefactor ε β) +
                  (C.predictedExponent - ε / 2) * L) := by
            rw [Real.exp_add, Real.exp_log hupperPos]
          _ < Real.exp ((C.predictedExponent - ε) * L) := by
            rw [Real.exp_lt_exp]
            linarith
      exact lt_trans hβpref.2 hexpUpper

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassPowerSandwich_of_boundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass :=
  freePositiveSubcriticalMassPowerSandwich_of_subpowerPrefactorSandwich
    C hmass
    (freePositiveSubcriticalMassSubpowerPrefactorSandwich_of_boundedPrefactorSandwich
      C hmass hbounded)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassPowerSandwich_of_constantPrefactorWeakSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass where
  δ := hconst.δ
  δ_pos := hconst.δ_pos
  δ_le_betaC := hconst.δ_le_betaC
  mass_pos := hconst.mass_pos
  mass_power_sandwich := by
    intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hlowerNegligible :
        Filter.Tendsto
          (fun β : ℝ =>
            Real.log (hconst.lowerPrefactor ε) /
              Real.log (Ising.betaC 3 - β))
          (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
          (nhds 0) := by
      simpa [Ising3DModel] using
        tendsto_log_bounded_prefactor_div_log_betaC_sub Ising3DModel
          (hconst.lowerPrefactor_pos ε hε)
          (hconst.lowerPrefactor_pos ε hε)
          (Filter.Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩)
    have hupperNegligible :
        Filter.Tendsto
          (fun β : ℝ =>
            Real.log (hconst.upperPrefactor ε) /
              Real.log (Ising.betaC 3 - β))
          (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
          (nhds 0) := by
      simpa [Ising3DModel] using
        tendsto_log_bounded_prefactor_div_log_betaC_sub Ising3DModel
          (hconst.upperPrefactor_pos ε hε)
          (hconst.upperPrefactor_pos ε hε)
          (Filter.Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩)
    have hlowerSmall :
        ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
          Real.log (hconst.lowerPrefactor ε) /
              Real.log (Ising.betaC 3 - β) <
            ε / 2 := by
      have hdist := (Metric.tendsto_nhds.mp hlowerNegligible) (ε / 2) hhalf
      filter_upwards [hdist] with β hβ
      rw [Real.dist_eq] at hβ
      exact (abs_lt.mp (by simpa using hβ)).2
    have hupperSmall :
        ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
          -(ε / 2) <
            Real.log (hconst.upperPrefactor ε) /
              Real.log (Ising.betaC 3 - β) := by
      have hdist := (Metric.tendsto_nhds.mp hupperNegligible) (ε / 2) hhalf
      filter_upwards [hdist] with β hβ
      rw [Real.dist_eq] at hβ
      exact (abs_lt.mp (by simpa using hβ)).1
    filter_upwards
      [hconst.mass_constant_prefactor_power_sandwich ε hε,
        hlowerSmall,
        hupperSmall,
        Ioo_mem_nhdsLT
          (show Ising.betaC 3 - 1 < Ising.betaC 3 by linarith)]
      with β hβpref hlowerSmallβ hupperSmallβ hβleft
    let m := freeSelectedPositiveSubcriticalMass hmass β
    let L := Real.log (Ising.betaC 3 - β)
    have hdist : Ising.betaC 3 - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβleft.1, hβleft.2]
    have hLneg : L < 0 := by
      simpa [L] using Real.log_neg hdist.1 hdist.2
    have hLne : L ≠ 0 := hLneg.ne
    constructor
    · have hlowerLog :
          (ε / 2) * L < Real.log (hconst.lowerPrefactor ε) := by
        calc
          (ε / 2) * L <
              (Real.log (hconst.lowerPrefactor ε) / L) * L := by
            exact mul_lt_mul_of_neg_right hlowerSmallβ hLneg
          _ = Real.log (hconst.lowerPrefactor ε) := by
            field_simp [hLne]
      have hexpLower :
          Real.exp ((C.predictedExponent + ε) * L) <
            hconst.lowerPrefactor ε *
              Real.exp ((C.predictedExponent + ε / 2) * L) := by
        calc
          Real.exp ((C.predictedExponent + ε) * L) <
              Real.exp
                (Real.log (hconst.lowerPrefactor ε) +
                  (C.predictedExponent + ε / 2) * L) := by
            rw [Real.exp_lt_exp]
            linarith
          _ =
              hconst.lowerPrefactor ε *
                Real.exp ((C.predictedExponent + ε / 2) * L) := by
            rw [Real.exp_add, Real.exp_log (hconst.lowerPrefactor_pos ε hε)]
      exact lt_of_lt_of_le hexpLower hβpref.1
    · have hupperLog :
          Real.log (hconst.upperPrefactor ε) < -(ε / 2) * L := by
        calc
          Real.log (hconst.upperPrefactor ε) =
              (Real.log (hconst.upperPrefactor ε) / L) * L := by
            field_simp [hLne]
          _ < -(ε / 2) * L := by
            exact mul_lt_mul_of_neg_right hupperSmallβ hLneg
      have hexpUpper :
          hconst.upperPrefactor ε *
              Real.exp ((C.predictedExponent - ε / 2) * L) <
            Real.exp ((C.predictedExponent - ε) * L) := by
        calc
          hconst.upperPrefactor ε *
              Real.exp ((C.predictedExponent - ε / 2) * L) =
              Real.exp
                (Real.log (hconst.upperPrefactor ε) +
                  (C.predictedExponent - ε / 2) * L) := by
            rw [Real.exp_add, Real.exp_log (hconst.upperPrefactor_pos ε hε)]
          _ < Real.exp ((C.predictedExponent - ε) * L) := by
            rw [Real.exp_lt_exp]
            linarith
      exact lt_of_le_of_lt hβpref.2 hexpUpper

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassPowerSandwich_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass :=
  freePositiveSubcriticalMassPowerSandwich_of_constantPrefactorWeakSandwich
    C hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakSandwich_of_constantPrefactorWeakIooSandwich
      C hmass hIoo)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassPowerSandwich_of_constantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C hmass) :
    FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass :=
  freePositiveSubcriticalMassPowerSandwich_of_constantPrefactorWeakIooSandwich
    C hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakIooSandwich_of_constantPrefactorWeakIooLowerUpper
      C hmass hlower hupper)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioSandwich_of_powerSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioSandwichNearCritical C hmass where
  δ := hpow.δ
  δ_pos := hpow.δ_pos
  δ_le_betaC := hpow.δ_le_betaC
  mass_pos := hpow.mass_pos
  log_mass_ratio_sandwich := by
    intro ε hε
    filter_upwards
      [hpow.mass_power_sandwich ε hε,
        Ioo_mem_nhdsLT
          (show Ising.betaC 3 - 1 < Ising.betaC 3 by linarith)]
      with β hβpow hβleft
    let m := freeSelectedPositiveSubcriticalMass hmass β
    let L := Real.log (Ising.betaC 3 - β)
    have hdist : Ising.betaC 3 - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβleft.1, hβleft.2]
    have hLneg : L < 0 := by
      simpa [L] using Real.log_neg hdist.1 hdist.2
    have hmpos : 0 < m := by
      exact lt_trans (Real.exp_pos _) hβpow.1
    have hlog_lower :
        (C.predictedExponent + ε) * L < Real.log m := by
      have hlog := Real.log_lt_log (Real.exp_pos _) hβpow.1
      simpa [m, L, Real.log_exp] using hlog
    have hlog_upper :
        Real.log m < (C.predictedExponent - ε) * L := by
      have hlog := Real.log_lt_log hmpos hβpow.2
      simpa [m, L, Real.log_exp] using hlog
    constructor
    · have hLpos : 0 < -L := neg_pos.mpr hLneg
      have hLne : L ≠ 0 := hLneg.ne
      change C.predictedExponent - ε < Real.log m / L
      refine lt_of_mul_lt_mul_right ?_ hLpos.le
      calc
        (C.predictedExponent - ε) * -L =
            -((C.predictedExponent - ε) * L) := by
          ring
        _ < -Real.log m := by
          linarith
        _ = (Real.log m / L) * -L := by
          field_simp [hLne]
    · have hLpos : 0 < -L := neg_pos.mpr hLneg
      have hLne : L ≠ 0 := hLneg.ne
      change Real.log m / L < C.predictedExponent + ε
      refine lt_of_mul_lt_mul_right ?_ hLpos.le
      calc
        (Real.log m / L) * -L = -Real.log m := by
          field_simp [hLne]
        _ < -((C.predictedExponent + ε) * L) := by
          linarith
        _ = (C.predictedExponent + ε) * -L := by
          ring

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass where
  δ := hsand.δ
  δ_pos := hsand.δ_pos
  δ_le_betaC := hsand.δ_le_betaC
  mass_pos := hsand.mass_pos
  log_mass_ratio_tendsto := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hsand.log_mass_ratio_sandwich ε hε] with β hβ
    rw [Real.dist_eq]
    exact abs_sub_lt_iff.mpr (by constructor <;> linarith [hβ.1, hβ.2])

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_powerSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_logRatioSandwich
    C hmass
    (freePositiveSubcriticalMassLogRatioSandwich_of_powerSandwich
      C hmass hpow)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_subpowerPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_powerSandwich
    C hmass
    (freePositiveSubcriticalMassPowerSandwich_of_subpowerPrefactorSandwich
      C hmass hsub)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_boundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_subpowerPrefactorSandwich
    C hmass
    (freePositiveSubcriticalMassSubpowerPrefactorSandwich_of_boundedPrefactorSandwich
      C hmass hbounded)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_powerSandwich
    C hmass
    (freePositiveSubcriticalMassPowerSandwich_of_constantPrefactorWeakSandwich
      C hmass hconst)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakSandwich
    C hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakSandwich_of_constantPrefactorWeakIooSandwich
      C hmass hIoo)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_fkBetaCIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooSandwich
    C hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakIooSandwich_of_fkBetaCIooSandwich
      C hmass hβeq hβc hsand)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_fkPCSelectedAgreementLogRatioLimit
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hratio :
      FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
        C hselected.fkMass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_fkBetaCIooSandwich
    C hmass hβeq hβc
    (freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCSelectedIooSandwich
      C hmass
      (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_exactPowerLaw
        C hmass hselected
        (freePositiveSubcriticalMassFKPCExactPowerLaw_of_logRatioLimit
          C hselected.fkMass hratio)))

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass :=
  freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooSandwich
    C hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakIooSandwich_of_constantPrefactorWeakIooLowerUpper
      C hmass hlower hupper)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass where
  δ := hratio.δ
  δ_pos := hratio.δ_pos
  δ_le_betaC := hratio.δ_le_betaC
  logRemainder := fun β =>
    Real.log (freeSelectedPositiveSubcriticalMass hmass β) -
      C.predictedExponent * Real.log (Ising.betaC 3 - β)
  mass_pos := hratio.mass_pos
  logRemainder_negligible := by
    let L := nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))
    have hconst :
        Filter.Tendsto (fun _ : ℝ => C.predictedExponent) L
          (nhds C.predictedExponent) :=
      tendsto_const_nhds
    have hshift :
        Filter.Tendsto
          (fun β : ℝ =>
            Real.log (freeSelectedPositiveSubcriticalMass hmass β) /
              Real.log (Ising.betaC 3 - β) -
                C.predictedExponent)
          L (nhds 0) := by
      simpa [L] using hratio.log_mass_ratio_tendsto.sub hconst
    refine Filter.Tendsto.congr' ?_ hshift
    filter_upwards
      [Ioo_mem_nhdsLT
        (show Ising.betaC 3 - 1 < Ising.betaC 3 by linarith)] with β hβ
    have hdiff : Ising.betaC 3 - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβ.1, hβ.2]
    have hden : Real.log (Ising.betaC 3 - β) ≠ 0 :=
      (Real.log_neg hdiff.1 hdiff.2).ne
    change
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) /
          Real.log (Ising.betaC 3 - β) -
            C.predictedExponent =
        (Real.log (freeSelectedPositiveSubcriticalMass hmass β) -
            C.predictedExponent * Real.log (Ising.betaC 3 - β)) /
          Real.log (Ising.betaC 3 - β)
    field_simp [hden]
  log_mass_scaling := by
    intro β hβ
    ring

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_logRatioSandwich
      C hmass hsand)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_powerSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_powerSandwich
      C hmass hpow)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_subpowerPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_subpowerPrefactorSandwich
      C hmass hsub)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_boundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_boundedPrefactorSandwich
      C hmass hbounded)

set_option linter.style.longLine false in

noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_constantPrefactorWeakSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakSandwich
      C hmass hconst)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooSandwich
      C hmass hIoo)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassLogAffineNearCritical_of_constantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C hmass) :
    FreePositiveSubcriticalMassLogAffineNearCritical C hmass :=
  freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooLowerUpper
      C hmass hlower hupper)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_logAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass where
  δ := hlog.δ
  δ_pos := hlog.δ_pos
  δ_le_betaC := hlog.δ_le_betaC
  massPrefactor := fun β => Real.exp (hlog.logRemainder β)
  massPrefactor_pos := by
    intro β hβ
    exact Real.exp_pos _
  massPrefactor_log_negligible := by
    simpa [Real.log_exp] using hlog.logRemainder_negligible
  mass_scaling := by
    intro β hβ
    have hmpos : 0 < freeSelectedPositiveSubcriticalMass hmass β :=
      hlog.mass_pos β hβ
    calc
      freeSelectedPositiveSubcriticalMass hmass β =
          Real.exp (Real.log (freeSelectedPositiveSubcriticalMass hmass β)) := by
        rw [Real.exp_log hmpos]
      _ =
          Real.exp
            (C.predictedExponent * Real.log (Ising.betaC 3 - β) +
              hlog.logRemainder β) := by
        rw [hlog.log_mass_scaling β hβ]
      _ =
          Real.exp (hlog.logRemainder β) *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
        rw [Real.exp_add, mul_comm]

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logAffineNearCritical
    C hmass
    (freePositiveSubcriticalMassLogAffineNearCritical_of_logRatioLimit
      C hmass hratio)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_logRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_logRatioSandwich
      C hmass hsand)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_powerSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_powerSandwich
      C hmass hpow)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_subpowerPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_subpowerPrefactorSandwich
      C hmass hsub)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_boundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_boundedPrefactorSandwich
      C hmass hbounded)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_constantPrefactorWeakSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakSandwich
      C hmass hconst)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_constantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooSandwich
      C hmass hIoo)

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassExactPowerLaw_of_constantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C hmass) :
    FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass :=
  freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
    C hmass
    (freePositiveSubcriticalMassLogRatioLimit_of_constantPrefactorWeakIooLowerUpper
      C hmass hlower hupper)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpower :
      FreePositiveSubcriticalMassExactPowerLawNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    hagree hmass hpower.δ hpower.δ_pos hpower.δ_le_betaC
    hpower.massPrefactor hpower.massPrefactor_pos
    hpower.massPrefactor_log_negligible hpower.mass_scaling

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassAsymptoticPowerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hasymp :
      FreePositiveSubcriticalMassAsymptoticPowerLawNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_asymptoticPowerLaw
      C hmass hasymp)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassLogAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlog :
      FreePositiveSubcriticalMassLogAffineNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_logAffineNearCritical
      C hmass hlog)

set_option linter.style.longLine false in

noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioLimit
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hratio :
      FreePositiveSubcriticalMassLogRatioLimitNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_logRatioLimit
      C hmass hratio)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassLogRatioSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsand :
      FreePositiveSubcriticalMassLogRatioSandwichNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_logRatioSandwich
      C hmass hsand)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassPowerSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpow :
      FreePositiveSubcriticalMassPowerSandwichNearCritical C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_powerSandwich
      C hmass hpow)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassSubpowerPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hsub :
      FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_subpowerPrefactorSandwich
      C hmass hsub)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassBoundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_boundedPrefactorSandwich
      C hmass hbounded)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hconst :
      FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_constantPrefactorWeakSandwich
      C hmass hconst)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hIoo :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_constantPrefactorWeakIooSandwich
      C hmass hIoo)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerUpper
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassExactPowerLaw
    C hagree hmass
    (freePositiveSubcriticalMassExactPowerLaw_of_constantPrefactorWeakIooLowerUpper
      C hmass hlower hupper)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooExistsLowerUpper
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerUpper
    C hagree hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakIooLower_of_exists
      C hmass hlower)
    (freePositiveSubcriticalMassConstantPrefactorWeakIooUpper_of_exists
      C hmass hupper)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooExistsLowerUpper
    C hagree hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakIooLowerExists_of_lowerBoundExists
      C hmass hlower)
    hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsUpperExists
    C hagree hmass
    (freePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExists_of_betaC_pos_noWindow
      C hmass hβc hlower)
    hupper

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCLowerBoundExistsNoWindowUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hlower :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
        C hmass)
    (hupper :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassConstantPrefactorWeakIooLowerBoundExistsNoWindowUpperExists
    C hagree hmass hβc
    (freePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindow_of_fkBetaC
      C hmass hβeq hlower)
    (freePositiveSubcriticalMassConstantPrefactorWeakIooUpperExists_of_fkBetaC
      C hmass hβeq hupper)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCIooSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hsand :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCLowerBoundExistsNoWindowUpperExists
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKBetaCLowerBoundExistsNoWindow_of_constantPrefactorWeakIooSandwich
      C hmass hsand)
    (freePositiveSubcriticalMassFKBetaCUpperExists_of_constantPrefactorWeakIooSandwich
      C hmass hsand)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCPullbackIooSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCIooSandwich
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCPullback
      C hmass hpull)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCCanonicalWindowPullbackIooSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCPullbackIooSandwich
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKPCPullback_of_canonicalWindowPullback
      C hmass hcanon)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedIooSandwich
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hp :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKBetaCIooSandwich
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCSelectedIooSandwich
      C hmass hp)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLowerUpper
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedIooSandwich
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lower_upper
      C hmass hselected hlower hupper)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementLowerUpperExists
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hlower :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C hselected.fkMass)
    (hupper :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedIooSandwich
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_lowerUpperExists
      C hmass hselected hlower hupper)

set_option linter.style.longLine false in


noncomputable def freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedAgreementExactPowerLaw
    (C : RGCertificate Ising3DModel)
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hβeq : Ising.betaC 3 = Ising3DFKBetaC)
    (hβc : 0 < Ising.betaC 3)
    (hselected :
      FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass)
    (hexact :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
        C hselected.fkMass) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C :=
  freeMassPowerLawToPlusTarget_of_freePositiveMassFKPCSelectedIooSandwich
    C hagree hmass hβeq hβc
    (freePositiveSubcriticalMassFKPCSelectedIooSandwich_of_agreement_exactPowerLaw
      C hmass hselected hexact)

end Exact3D
end StatMech
