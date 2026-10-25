/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierC/IsingTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DetLoopExpansion
import Theorem.StatisticalMechanics.Code.Onsager.TracePowWalk
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Order.Filter.AtTopBot.Basic
import Def.StatisticalMechanics.Code.FrontierC.IsingTransfer.Part3
open scoped BigOperators
open Matrix Polynomial


namespace StatMech.FrontierC

lemma isingTransfer_apply (beta h : ℝ) (s t : Fin 2) :
    isingTransfer beta h s t =
      (Real.exp (beta * transferSpin s * transferSpin t +
        (h / 2) * (transferSpin s + transferSpin t)) : ℂ) := by
  fin_cases s <;> fin_cases t <;>
    simp [isingTransfer, isingTransferReal, transferSpin] <;>
    congr 2 <;> ring

lemma sum_transferSpin_add_one {n : ℕ} [NeZero n] (s : Fin n → Fin 2) :
    (∑ k : Fin n, transferSpin (s (k + 1))) =
      ∑ k : Fin n, transferSpin (s k) := by
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin n))
    (fun k => transferSpin (s k))

lemma isingTransfer_loopWeight {n : ℕ} [NeZero n]
    (beta h : ℝ) (s : Fin n → Fin 2) :
    (∏ k : Fin n, isingTransfer beta h (s k) (s (k + 1))) =
      (Real.exp (isingRingExponent beta h s) : ℂ) := by
  simp_rw [isingTransfer_apply]
  change (∏ k : Fin n, algebraMap ℝ ℂ
      (Real.exp (beta * transferSpin (s k) * transferSpin (s (k + 1)) +
        (h / 2) * (transferSpin (s k) + transferSpin (s (k + 1)))))) =
    algebraMap ℝ ℂ (Real.exp (isingRingExponent beta h s))
  rw [← map_prod, ← Real.exp_sum]
  congr 2
  rw [isingRingExponent, Finset.sum_add_distrib]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_transferSpin_add_one]
  ring


theorem isingRingZ_eq_trace (n : ℕ) [NeZero n] (hn : 0 < n) (beta h : ℝ) :
    (isingRingZ n beta h : ℂ) = ((isingTransfer beta h) ^ n).trace := by
  rw [StatMech.Onsager.ons_trace_pow_eq_walk_sum _ n hn]
  rw [isingRingZ]
  change algebraMap ℝ ℂ (∑ s : Fin n → Fin 2,
      Real.exp (isingRingExponent beta h s)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun s _ => (isingTransfer_loopWeight beta h s).symm)


theorem isingRingZ_eigenvalues (n : ℕ) [NeZero n] (hn : 0 < n) (beta h : ℝ) :
    (isingRingZ n beta h : ℂ) =
      (isingTransferEigenPlus beta h : ℂ) ^ n +
      (isingTransferEigenMinus beta h : ℂ) ^ n := by
  rw [isingRingZ_eq_trace n hn, isingTransfer_trace_pow]


theorem isingRingZ_eigenvalues_real (n : ℕ) [NeZero n] (hn : 0 < n)
    (beta h : ℝ) :
    isingRingZ n beta h =
      isingTransferEigenPlus beta h ^ n +
      isingTransferEigenMinus beta h ^ n := by
  exact_mod_cast isingRingZ_eigenvalues n hn beta h

lemma isingRingZ_pos (n : ℕ) [NeZero n] (beta h : ℝ) :
    0 < isingRingZ n beta h := by
  unfold isingRingZ
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty


lemma isingTransfer_abs_eigenMinus_lt (beta h : ℝ) :
    |isingTransferEigenMinus beta h| < isingTransferEigenPlus beta h := by
  have hs : 0 < transferA beta h + transferD beta h :=
    add_pos (Real.exp_pos _) (Real.exp_pos _)
  have hd := isingTransfer_disc_pos beta h
  rw [abs_lt]
  simp only [isingTransferEigenPlus, isingTransferEigenMinus]
  constructor <;> linarith

lemma isingTransfer_eigenRatio_abs_lt_one (beta h : ℝ) :
    |isingTransferEigenMinus beta h / isingTransferEigenPlus beta h| < 1 := by
  rw [abs_div, abs_of_pos (isingTransfer_eigenPlus_pos beta h),
    div_lt_one (isingTransfer_eigenPlus_pos beta h)]
  exact isingTransfer_abs_eigenMinus_lt beta h

lemma isingRing_spectral_factor (beta h : ℝ) (n : ℕ) :
    isingTransferEigenPlus beta h ^ n + isingTransferEigenMinus beta h ^ n =
      isingTransferEigenPlus beta h ^ n *
        (1 + (isingTransferEigenMinus beta h /
          isingTransferEigenPlus beta h) ^ n) := by
  have hp : isingTransferEigenPlus beta h ≠ 0 :=
    (isingTransfer_eigenPlus_pos beta h).ne'
  rw [div_pow]
  field_simp [pow_ne_zero _ hp]

lemma isingRing_ratio_factor_pos (beta h : ℝ) (n : ℕ) :
    0 < 1 + (isingTransferEigenMinus beta h /
      isingTransferEigenPlus beta h) ^ (n + 1) := by
  let r := isingTransferEigenMinus beta h / isingTransferEigenPlus beta h
  have hr : |r| < 1 := isingTransfer_eigenRatio_abs_lt_one beta h
  have hrpow : |r ^ (n + 1)| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg r) hr (by omega)
  rw [abs_lt] at hrpow
  linarith


theorem isingRing_pressure_tendsto (beta h : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => Real.log (isingRingZ (n + 1) beta h) / (n + 1 : ℝ))
      Filter.atTop
      (nhds (Real.log (isingTransferEigenPlus beta h))) := by
  let r := isingTransferEigenMinus beta h / isingTransferEigenPlus beta h
  have hr : |r| < 1 := isingTransfer_eigenRatio_abs_lt_one beta h
  have hshift : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with n hn
    omega
  have hrpow : Filter.Tendsto (fun n : ℕ => r ^ (n + 1)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).comp hshift
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (1 + r ^ (n + 1)))
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.add hrpow).log
      (by norm_num : (1 : ℝ) + 0 ≠ 0) using 1
    all_goals norm_num
  have hden : Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ)) Filter.atTop Filter.atTop :=
    by
      rw [Filter.tendsto_atTop]
      intro b
      obtain ⟨N, hN⟩ := exists_nat_ge b
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
  have herr : Filter.Tendsto
      (fun n : ℕ => Real.log (1 + r ^ (n + 1)) / (n + 1 : ℝ))
      Filter.atTop (nhds 0) := by
    simpa using hlog.div_atTop hden
  have htotal : Filter.Tendsto
      (fun n : ℕ => Real.log (isingTransferEigenPlus beta h) +
        Real.log (1 + r ^ (n + 1)) / (n + 1 : ℝ))
      Filter.atTop (nhds (Real.log (isingTransferEigenPlus beta h))) := by
    simpa using (tendsto_const_nhds.add herr)
  refine htotal.congr' (Filter.Eventually.of_forall ?_)
  intro n
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have hn : 0 < n + 1 := Nat.zero_lt_succ n
  have hp : 0 < isingTransferEigenPlus beta h :=
    isingTransfer_eigenPlus_pos beta h
  have hf : 0 < 1 + r ^ (n + 1) := isingRing_ratio_factor_pos beta h n
  change Real.log (isingTransferEigenPlus beta h) +
      Real.log (1 + r ^ (n + 1)) / (n + 1 : ℝ) =
    Real.log (isingRingZ (n + 1) beta h) / (n + 1 : ℝ)
  rw [isingRingZ_eigenvalues_real (n + 1) hn,
    isingRing_spectral_factor, Real.log_mul (pow_ne_zero _ hp.ne') hf.ne',
    Real.log_pow]
  dsimp only [r]
  field_simp
  push_cast
  ring

lemma transfer_sum_closed_form (beta h : ℝ) :
    transferA beta h + transferD beta h =
      2 * Real.exp beta * Real.cosh h := by
  rw [transferA, transferD, Real.exp_add, Real.exp_sub, Real.cosh_eq,
    Real.exp_neg]
  field_simp [Real.exp_ne_zero]

lemma transfer_diff_closed_form (beta h : ℝ) :
    transferA beta h - transferD beta h =
      2 * Real.exp beta * Real.sinh h := by
  rw [transferA, transferD, Real.exp_add, Real.exp_sub, Real.sinh_eq,
    Real.exp_neg]
  field_simp [Real.exp_ne_zero]

lemma transferB_sq_closed_form (beta : ℝ) :
    transferB beta ^ 2 = Real.exp (-2 * beta) := by
  rw [transferB, pow_two, ← Real.exp_add]
  congr 1
  ring

lemma exp_sq_closed_form (beta : ℝ) :
    Real.exp beta ^ 2 = Real.exp (2 * beta) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring


theorem isingTransferEigenPlus_closed_form (beta h : ℝ) :
    isingTransferEigenPlus beta h =
      Real.exp beta * Real.cosh h +
        Real.sqrt (Real.exp (2 * beta) * Real.sinh h ^ 2 +
          Real.exp (-2 * beta)) := by
  have hdisc : isingTransferDisc beta h =
      2 * Real.sqrt (Real.exp (2 * beta) * Real.sinh h ^ 2 +
        Real.exp (-2 * beta)) := by
    rw [isingTransferDisc, transfer_diff_closed_form,
      transferB_sq_closed_form, show
        (2 * Real.exp beta * Real.sinh h) ^ 2 + 4 * Real.exp (-2 * beta) =
          4 * (Real.exp (2 * beta) * Real.sinh h ^ 2 +
            Real.exp (-2 * beta)) by
        rw [← exp_sq_closed_form beta]
        ring]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [isingTransferEigenPlus, transfer_sum_closed_form, hdisc]
  ring


theorem isingRing_pressure_closed_form (beta h : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => Real.log (isingRingZ (n + 1) beta h) / (n + 1 : ℝ))
      Filter.atTop
      (nhds (Real.log (Real.exp beta * Real.cosh h +
        Real.sqrt (Real.exp (2 * beta) * Real.sinh h ^ 2 +
          Real.exp (-2 * beta))))) := by
  simpa only [isingTransferEigenPlus_closed_form] using
    isingRing_pressure_tendsto beta h


end StatMech.FrontierC
