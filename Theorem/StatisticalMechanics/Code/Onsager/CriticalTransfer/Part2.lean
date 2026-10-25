/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CriticalTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.FreeEnergy
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Def.StatisticalMechanics.Code.Onsager.CriticalTransfer


namespace StatMech.Onsager

open StatMech.Ising

theorem ons_torusPressureSeq_lipschitz (beta gamma : ℝ) (L : ℕ) :
    |ons_torusPressureSeq beta L - ons_torusPressureSeq gamma L| ≤
      2 * |beta - gamma| := by
  by_cases hL : 2 < L
  · letI : Fact (2 < L) := ⟨hL⟩
    simpa [ons_torusPressureSeq, hL] using
      ons_torusPressure_lipschitz L beta gamma
  · simp [ons_torusPressureSeq, hL]


theorem ons_free_energy_critical_of_noncritical
    (hcontinuous : ContinuousAt ons_pressure ons_betaC)
    (hnoncritical : ∀ beta : ℝ, 0 ≤ beta → beta ≠ ons_betaC →
      Filter.Tendsto (ons_torusPressureSeq beta)
        Filter.atTop (nhds (ons_pressure beta))) :
    Filter.Tendsto (ons_torusPressureSeq ons_betaC)
      Filter.atTop (nhds (ons_pressure ons_betaC)) := by
  let gamma : ℕ → ℝ := fun n => ons_betaC + 1 / ((n : ℝ) + 1)
  have hgamma : Filter.Tendsto gamma Filter.atTop (nhds ons_betaC) := by
    simpa only [gamma, add_zero] using
      (tendsto_const_nhds.add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hpressure : Filter.Tendsto (fun n => ons_pressure (gamma n))
      Filter.atTop (nhds (ons_pressure ons_betaC)) :=
    hcontinuous.tendsto.comp hgamma
  rw [Metric.tendsto_atTop] at hpressure hgamma ⊢
  intro epsilon hepsilon
  obtain ⟨Npressure, hNpressure⟩ := hpressure (epsilon / 3) (by positivity)
  obtain ⟨Ngamma, hNgamma⟩ := hgamma (epsilon / 6) (by positivity)
  let n := max Npressure Ngamma
  have hnpressure :
      dist (ons_pressure (gamma n)) (ons_pressure ons_betaC) < epsilon / 3 :=
    hNpressure n (le_max_left _ _)
  have hngamma : dist (gamma n) ons_betaC < epsilon / 6 :=
    hNgamma n (le_max_right _ _)
  have hgpos : 0 < gamma n := by
    dsimp only [gamma]
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hone : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hden
    linarith [ons_betaC_pos]
  have hgne : gamma n ≠ ons_betaC := by
    dsimp only [gamma]
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hone : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hden
    linarith
  have hfixed := hnoncritical (gamma n) hgpos.le hgne
  rw [Metric.tendsto_atTop] at hfixed
  obtain ⟨Nfixed, hNfixed⟩ := hfixed (epsilon / 3) (by positivity)
  refine ⟨Nfixed, fun L hL => ?_⟩
  have hmiddle := hNfixed L hL
  have hfinite := ons_torusPressureSeq_lipschitz ons_betaC (gamma n) L
  rw [Real.dist_eq] at hmiddle hnpressure hngamma ⊢
  calc
    |ons_torusPressureSeq ons_betaC L - ons_pressure ons_betaC| ≤
        |ons_torusPressureSeq ons_betaC L - ons_torusPressureSeq (gamma n) L| +
          |ons_torusPressureSeq (gamma n) L - ons_pressure (gamma n)| +
          |ons_pressure (gamma n) - ons_pressure ons_betaC| := by
      calc
        |ons_torusPressureSeq ons_betaC L - ons_pressure ons_betaC| ≤
            |ons_torusPressureSeq ons_betaC L - ons_torusPressureSeq (gamma n) L| +
              |ons_torusPressureSeq (gamma n) L - ons_pressure ons_betaC| :=
          abs_sub_le _ _ _
        _ ≤ |ons_torusPressureSeq ons_betaC L - ons_torusPressureSeq (gamma n) L| +
            (|ons_torusPressureSeq (gamma n) L - ons_pressure (gamma n)| +
              |ons_pressure (gamma n) - ons_pressure ons_betaC|) := by
          gcongr
          exact abs_sub_le _ _ _
        _ = _ := by ring
    _ < 2 * (epsilon / 6) + epsilon / 3 + epsilon / 3 := by
      gcongr
      calc
        |ons_torusPressureSeq ons_betaC L - ons_torusPressureSeq (gamma n) L| ≤
            2 * |ons_betaC - gamma n| := hfinite
        _ = 2 * |gamma n - ons_betaC| := by rw [abs_sub_comm]
        _ < 2 * (epsilon / 6) := by gcongr
    _ = epsilon := by ring

end StatMech.Onsager
