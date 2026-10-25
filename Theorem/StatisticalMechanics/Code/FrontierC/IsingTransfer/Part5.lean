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
import Def.StatisticalMechanics.Code.FrontierC.IsingTransfer.Part5
open scoped BigOperators
open Matrix Polynomial


namespace StatMech.FrontierC

lemma transferAD_closed_form (beta h : ℝ) :
    transferA beta h * transferD beta h = Real.exp (2 * beta) := by
  rw [transferA, transferD, ← Real.exp_add]
  congr 1
  ring

lemma isingTransfer_eigenMinus_nonneg {beta : ℝ} (hbeta : 0 ≤ beta) (h : ℝ) :
    0 ≤ isingTransferEigenMinus beta h := by
  have hexp : Real.exp (-2 * beta) ≤ Real.exp (2 * beta) := by
    rw [Real.exp_le_exp]
    linarith
  have hprod : 0 ≤ isingTransferEigenPlus beta h *
      isingTransferEigenMinus beta h := by
    rw [isingTransfer_eigen_prod, transferAD_closed_form,
      transferB_sq_closed_form]
    linarith
  nlinarith [isingTransfer_eigenPlus_pos beta h]


theorem isingTransferCorrelationRatio_mem_Ico {beta : ℝ} (hbeta : 0 ≤ beta)
    (h : ℝ) : isingTransferCorrelationRatio beta h ∈ Set.Ico 0 1 := by
  have hnonneg : 0 ≤ isingTransferCorrelationRatio beta h :=
    div_nonneg (isingTransfer_eigenMinus_nonneg hbeta h)
      (isingTransfer_eigenPlus_pos beta h).le
  refine ⟨hnonneg, ?_⟩
  have habs := isingTransfer_eigenRatio_abs_lt_one beta h
  change |isingTransferCorrelationRatio beta h| < 1 at habs
  rw [abs_of_nonneg hnonneg] at habs
  exact habs


theorem isingTransferCorrelationRatio_pow_tendsto_zero {beta : ℝ}
    (hbeta : 0 ≤ beta) (h : ℝ) :
    Filter.Tendsto (fun n : ℕ => isingTransferCorrelationRatio beta h ^ n)
      Filter.atTop (nhds 0) := by
  have hr := isingTransferCorrelationRatio_mem_Ico hbeta h
  apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
  rw [abs_of_nonneg hr.1]
  exact hr.2

end StatMech.FrontierC
