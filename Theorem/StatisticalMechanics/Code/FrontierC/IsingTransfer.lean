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
import Def.StatisticalMechanics.Code.FrontierC.IsingTransfer
open scoped BigOperators
open Matrix Polynomial


namespace StatMech.FrontierC

lemma isingTransfer_disc_sq (beta h : ℝ) :
    isingTransferDisc beta h ^ 2 =
      (transferA beta h - transferD beta h) ^ 2 +
        4 * transferB beta ^ 2 := by
  rw [isingTransferDisc, Real.sq_sqrt]
  positivity

lemma isingTransfer_eigen_sum (beta h : ℝ) :
    isingTransferEigenPlus beta h + isingTransferEigenMinus beta h =
      transferA beta h + transferD beta h := by
  simp only [isingTransferEigenPlus, isingTransferEigenMinus]
  ring

lemma isingTransfer_eigen_prod (beta h : ℝ) :
    isingTransferEigenPlus beta h * isingTransferEigenMinus beta h =
      transferA beta h * transferD beta h - transferB beta ^ 2 := by
  have hs := isingTransfer_disc_sq beta h
  simp only [isingTransferEigenPlus, isingTransferEigenMinus]
  nlinarith

lemma isingTransfer_disc_pos (beta h : ℝ) : 0 < isingTransferDisc beta h := by
  rw [isingTransferDisc]
  apply Real.sqrt_pos.2
  have hb : 0 < transferB beta := Real.exp_pos _
  nlinarith [sq_nonneg (transferA beta h - transferD beta h)]

lemma isingTransfer_eigenPlus_pos (beta h : ℝ) :
    0 < isingTransferEigenPlus beta h := by
  have ha : 0 < transferA beta h := Real.exp_pos _
  have hd : 0 < transferD beta h := Real.exp_pos _
  have hs := isingTransfer_disc_pos beta h
  rw [isingTransferEigenPlus]
  positivity

lemma isingTransfer_trace (beta h : ℝ) :
    (isingTransfer beta h).trace =
      ((transferA beta h + transferD beta h : ℝ) : ℂ) := by
  simp [isingTransfer, isingTransferReal, Matrix.trace_fin_two,
    transferA, transferD]

lemma isingTransfer_det (beta h : ℝ) :
    (isingTransfer beta h).det =
      ((transferA beta h * transferD beta h - transferB beta ^ 2 : ℝ) : ℂ) := by
  simp [isingTransfer, isingTransferReal, Matrix.det_fin_two,
    transferA, transferB, transferD]
  ring_nf


theorem isingTransfer_charpoly (beta h : ℝ) :
    (isingTransfer beta h).charpoly =
      (X - C (isingTransferEigenPlus beta h : ℂ)) *
      (X - C (isingTransferEigenMinus beta h : ℂ)) := by
  rw [Matrix.charpoly_fin_two, isingTransfer_trace, isingTransfer_det]
  rw [← isingTransfer_eigen_sum beta h, ← isingTransfer_eigen_prod beta h]
  push_cast
  simp only [map_add, map_mul]
  ring

lemma isingTransfer_roots (beta h : ℝ) :
    (isingTransfer beta h).charpoly.roots =
      {(isingTransferEigenPlus beta h : ℂ),
       (isingTransferEigenMinus beta h : ℂ)} := by
  rw [isingTransfer_charpoly, roots_mul]
  · simp [roots_X_sub_C]
  · exact mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)


theorem isingTransfer_trace_pow (beta h : ℝ) (n : ℕ) :
    ((isingTransfer beta h) ^ n).trace =
      (isingTransferEigenPlus beta h : ℂ) ^ n +
      (isingTransferEigenMinus beta h : ℂ) ^ n := by
  have htoLin_pow : ((isingTransfer beta h) ^ n).toLin' =
      (isingTransfer beta h).toLin' ^ n := by
    induction n with
    | zero => simp [Matrix.toLin'_one, Module.End.one_eq_id]
    | succ n ih =>
        rw [pow_succ, Matrix.toLin'_mul, ih, pow_succ, Module.End.mul_eq_comp]
  rw [← Matrix.trace_toLin'_eq, htoLin_pow,
    StatMech.Onsager.trace_pow_endo, Matrix.charpoly_toLin',
    isingTransfer_roots]
  simp


end StatMech.FrontierC
