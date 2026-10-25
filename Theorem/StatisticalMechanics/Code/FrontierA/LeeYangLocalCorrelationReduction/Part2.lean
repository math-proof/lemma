/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangPressurePrimitive.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxSpinLimit
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Def.StatisticalMechanics.Code.FrontierA.LeeYangLocalCorrelationReduction.Part2
open Complex Filter MeasureTheory Metric Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.FK StatMech.Ising StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierC StatMech.Sharpness StatMech.Sharpness.FieldGhostDict


theorem continuousOn_leeYangSpinProductRightEnvelope
    {beta : ℝ} (hbeta : 0 < beta) (A : Finset (Site d)) :
    ContinuousOn (leeYangSpinProductRightEnvelope beta A)
      {h : ℂ | 0 < h.re} := by
  have hr : Continuous
      (fun h : ℂ => ‖Complex.exp (-2 * (beta : ℂ) * h)‖) := by
    fun_prop
  apply ContinuousOn.pow
  apply ContinuousOn.div
  · exact continuousOn_const.add hr.continuousOn
  · exact continuousOn_const.sub hr.continuousOn
  · intro h hh
    change 0 < h.re at hh
    have hnorm : ‖Complex.exp (-2 * (beta : ℂ) * h)‖ < 1 := by
      rw [Complex.norm_exp, Real.exp_lt_one_iff]
      norm_num [Complex.mul_re]
      nlinarith
    simpa only [sub_ne_zero] using ne_of_gt hnorm

theorem continuousOn_leeYangSpinProductLeftEnvelope
    {beta : ℝ} (hbeta : 0 < beta) (A : Finset (Site d)) :
    ContinuousOn (leeYangSpinProductLeftEnvelope beta A)
      {h : ℂ | h.re < 0} := by
  have hr : Continuous
      (fun h : ℂ => ‖Complex.exp (2 * (beta : ℂ) * h)‖) := by
    fun_prop
  apply ContinuousOn.pow
  apply ContinuousOn.div
  · exact continuousOn_const.add hr.continuousOn
  · exact continuousOn_const.sub hr.continuousOn
  · intro h hh
    change h.re < 0 at hh
    have hnorm : ‖Complex.exp (2 * (beta : ℂ) * h)‖ < 1 := by
      rw [Complex.norm_exp, Real.exp_lt_one_iff]
      norm_num [Complex.mul_re]
      nlinarith
    simpa only [sub_ne_zero] using ne_of_gt hnorm


end StatMech.FrontierA
