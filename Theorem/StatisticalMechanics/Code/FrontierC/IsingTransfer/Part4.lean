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
import Def.StatisticalMechanics.Code.FrontierC.IsingTransfer.Part4
open scoped BigOperators
open Matrix Polynomial


namespace StatMech.FrontierC

lemma isingPressureRadicand_pos (x : ℝ × ℝ) :
    0 < isingPressureRadicand x := by
  unfold isingPressureRadicand
  positivity

lemma isingPressure_sqrt_eq_exp (x : ℝ × ℝ) :
    Real.sqrt (isingPressureRadicand x) =
      Real.exp (Real.log (isingPressureRadicand x) / 2) := by
  apply (Real.sqrt_eq_iff_eq_sq (isingPressureRadicand_pos x).le
    (Real.exp_pos _).le).2
  rw [pow_two, ← Real.exp_add]
  rw [show Real.log (isingPressureRadicand x) / 2 +
      Real.log (isingPressureRadicand x) / 2 =
      Real.log (isingPressureRadicand x) by ring,
    Real.exp_log (isingPressureRadicand_pos x)]

theorem analyticAt_isingPressureRadicand (x : ℝ × ℝ) :
    AnalyticAt ℝ isingPressureRadicand x := by
  have hfst : AnalyticAt ℝ (fun y : ℝ × ℝ => y.1) x := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun y : ℝ × ℝ => y.2) x := analyticAt_snd
  have htwoFst : AnalyticAt ℝ (fun y : ℝ × ℝ => 2 * y.1) x :=
    analyticAt_const.mul hfst
  have hnegTwoFst : AnalyticAt ℝ (fun y : ℝ × ℝ => -2 * y.1) x :=
    analyticAt_const.mul hfst
  unfold isingPressureRadicand
  exact (htwoFst.rexp'.mul
    ((Real.analyticAt_sinh.comp hsnd).pow 2)).add hnegTwoFst.rexp'


theorem isingPressureClosedForm_analyticAt (x : ℝ × ℝ) :
    AnalyticAt ℝ isingPressureClosedForm x := by
  have hsqrtAlt : AnalyticAt ℝ
      (fun y : ℝ × ℝ =>
        Real.exp (Real.log (isingPressureRadicand y) / 2)) x := by
    exact ((analyticAt_log (isingPressureRadicand_pos x)).comp
      (analyticAt_isingPressureRadicand x)).div_const.rexp'
  have hsqrt : AnalyticAt ℝ
      (fun y : ℝ × ℝ => Real.sqrt (isingPressureRadicand y)) x := by
    exact hsqrtAlt.congr (Filter.Eventually.of_forall fun y =>
      (isingPressure_sqrt_eq_exp y).symm)
  have hlambda : AnalyticAt ℝ
      (fun y : ℝ × ℝ => Real.exp y.1 * Real.cosh y.2 +
        Real.sqrt (isingPressureRadicand y)) x := by
    have hfst : AnalyticAt ℝ (fun y : ℝ × ℝ => y.1) x := analyticAt_fst
    have hsnd : AnalyticAt ℝ (fun y : ℝ × ℝ => y.2) x := analyticAt_snd
    apply AnalyticAt.add
    · exact hfst.rexp'.mul (Real.analyticAt_cosh.comp hsnd)
    · exact hsqrt
  have hlambdaPos : 0 < Real.exp x.1 * Real.cosh x.2 +
      Real.sqrt (isingPressureRadicand x) := by
    positivity
  unfold isingPressureClosedForm
  change AnalyticAt ℝ
    (fun y : ℝ × ℝ => Real.log (Real.exp y.1 * Real.cosh y.2 +
      Real.sqrt (isingPressureRadicand y))) x
  exact AnalyticAt.comp'
    (f := fun y : ℝ × ℝ => Real.exp y.1 * Real.cosh y.2 +
      Real.sqrt (isingPressureRadicand y))
    (analyticAt_log hlambdaPos) hlambda


end StatMech.FrontierC
