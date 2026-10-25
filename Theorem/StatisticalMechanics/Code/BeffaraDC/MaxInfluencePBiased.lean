/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/MaxInfluencePBiased.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.MaxInfluenceHalf
import Theorem.StatisticalMechanics.Code.Probability.NearHalfBKKKL
import Theorem.StatisticalMechanics.Code.Probability.PBiasedKKLClose
open scoped BigOperators
open Finset Real Set


namespace StatMech.BeffaraDC

open StatMech ConfigSpace Probability OSSS TwoDim

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem maxInfl_ge_scaled_var_mul_log_card_of_logGain [Nonempty E]
    {p c : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hc0 : 0 ≤ c) (hc2 : c ≤ 2)
    (φ : ConfigSpace E → Bool)
    (hgain : c * OSSS.var (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / Probability.maxInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ Probability.totalInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0)) :
    (c / 2) * OSSS.var (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (Fintype.card E : ℝ) / (Fintype.card E : ℝ)
      ≤ Probability.maxInfl (OSSS.bernoulliWeight p)
          (fun ω => if φ ω then (1 : ℝ) else 0) := by
  let f : ConfigSpace E → ℝ := fun ω => if φ ω then 1 else 0
  let n : ℝ := Fintype.card E
  let V : ℝ := OSSS.var (OSSS.bernoulliWeight p) f
  let δ : ℝ := Probability.maxInfl (OSSS.bernoulliWeight p) f
  change (c / 2) * V * Real.log n / n ≤ δ
  have hcard : 0 < Fintype.card E := Fintype.card_pos
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast hcard
  have hn0 : 0 ≤ n := hn.le
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have hs0 : 0 ≤ Real.sqrt n := hs.le
  have hs_sq : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn0
  have hprob := OSSS.bernoulliWeight_isProbWeight (E := E) hp0.le hp1.le
  have hV0 : 0 ≤ V := by
    dsimp [V]
    exact Probability.kkl_var_nonneg hprob f
  have hV4 : V ≤ 1 / 4 := by
    dsimp [V, f]
    exact Probability.kkl_var_le_quarter _ φ
  have hδ0 : 0 ≤ δ := by
    dsimp [δ]
    exact Probability.kkl_maxInfl_nonneg hprob f
  have hlog0 : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    dsimp [n]
    exact_mod_cast (Nat.one_le_iff_ne_zero.2 hcard.ne')
  have hlog_upper : Real.log n ≤ 2 * Real.sqrt n := by
    have h := Real.log_natCast_le_rpow_div (Fintype.card E)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    norm_num at h ⊢
    simpa [n, mul_comm] using h
  have hKKL : c * V * Real.log (1 / δ) ≤ n * δ := by
    have havg : Probability.totalInfl (OSSS.bernoulliWeight p) f ≤ n * δ := by
      simpa [n, δ] using Probability.kkl_maxInfl_ge_avg
        (OSSS.bernoulliWeight p) f
    have hg : c * V * Real.log (1 / δ) ≤
        Probability.totalInfl (OSSS.bernoulliWeight p) f := by
      simpa [V, δ, f] using hgain
    exact hg.trans havg
  by_cases hlarge : 1 / Real.sqrt n ≤ δ
  · have hcdiv : c / 2 ≤ 1 := by linarith
    have hscaled : (c / 2) * V * Real.log n ≤ V * Real.log n := by
      have hVL0 : 0 ≤ V * Real.log n := mul_nonneg hV0 hlog0
      calc
        (c / 2) * V * Real.log n = (c / 2) * (V * Real.log n) := by ring
        _ ≤ 1 * (V * Real.log n) :=
          mul_le_mul_of_nonneg_right hcdiv hVL0
        _ = V * Real.log n := one_mul _
    have hVL : V * Real.log n ≤ (1 / 4 : ℝ) * (2 * Real.sqrt n) :=
      mul_le_mul hV4 hlog_upper hlog0 (by norm_num)
    have hscale_eq : ((1 / 4 : ℝ) * (2 * Real.sqrt n)) / n
        = 1 / (2 * Real.sqrt n) := by
      field_simp [hn.ne', hs.ne']
      nlinarith [hs_sq]
    have hscale : ((1 / 4 : ℝ) * (2 * Real.sqrt n)) / n
        ≤ 1 / Real.sqrt n := by
      rw [hscale_eq]
      field_simp [hs.ne']
      nlinarith [hs]
    calc
      (c / 2) * V * Real.log n / n ≤ (V * Real.log n) / n :=
        div_le_div_of_nonneg_right hscaled hn0
      _ ≤ ((1 / 4 : ℝ) * (2 * Real.sqrt n)) / n :=
        div_le_div_of_nonneg_right hVL hn0
      _ ≤ 1 / Real.sqrt n := hscale
      _ ≤ δ := hlarge
  · have hsmall : δ < 1 / Real.sqrt n := lt_of_not_ge hlarge
    rcases hδ0.eq_or_lt with hδ | hδ
    · have hδz : δ = 0 := hδ.symm
      have htotal : Probability.totalInfl (OSSS.bernoulliWeight p) f ≤ n * δ := by
        simpa [n, δ] using Probability.kkl_maxInfl_ge_avg
          (OSSS.bernoulliWeight p) f
      have hpoincare : V ≤ Probability.totalInfl (OSSS.bernoulliWeight p) f := by
        dsimp [V]
        exact Probability.kkl_var_le_total_influence hprob φ
      have hV : V = 0 := by
        have : V ≤ 0 := by simpa [hδz] using hpoincare.trans htotal
        exact le_antisymm this hV0
      simp [hV, hδz]
    · have hs_le_inv : Real.sqrt n ≤ 1 / δ := by
        rw [le_div_iff₀ hδ]
        have hmul := (lt_div_iff₀ hs).mp hsmall
        simpa [mul_comm] using hmul.le
      have hlog_lower : Real.log n / 2 ≤ Real.log (1 / δ) := by
        rw [← Real.log_sqrt hn0]
        exact Real.log_le_log hs hs_le_inv
      have hVlog : (c / 2) * V * Real.log n
          ≤ c * V * Real.log (1 / δ) := by
        have hmul := mul_le_mul_of_nonneg_left hlog_lower (mul_nonneg hc0 hV0)
        nlinarith
      have hmain : (c / 2) * V * Real.log n ≤ n * δ := hVlog.trans hKKL
      exact (div_le_iff₀ hn).2 (by simpa [mul_comm] using hmain)


end StatMech.BeffaraDC
