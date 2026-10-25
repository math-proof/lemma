/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDualGapAsymptotic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDualGapAsymptotic.Part2
open Filter Topology
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDualGapRate_div_tendsto_one :
    Tendsto (fun lam : Real =>
      sixVertexDualGapRate lam /
        (8 * Real.exp (-(Real.pi ^ 2) / (2 * lam))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  apply sixVertexDualGapPowerSeries_div_tendsto_one.comp
  have hdiv : Tendsto (fun lam : Real => -(Real.pi ^ 2) / (2 * lam))
      (nhdsWithin 0 (Set.Ioi 0)) atBot := by
      rw [Filter.tendsto_atBot]
      intro b
      have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      filter_upwards [Ioo_mem_nhdsGT
        (show 0 < Real.pi ^ 2 / (2 * (|b| + 1)) by positivity)] with lam hlam
      have hlam0 : 0 < lam := hlam.1
      have hlamUpper : lam < Real.pi ^ 2 / (2 * (|b| + 1)) := hlam.2
      have hb : -(|b| + 1) < b := by
        nlinarith [neg_abs_le b]
      have hcore : 2 * lam * (|b| + 1) < Real.pi ^ 2 := by
        rw [lt_div_iff₀ (show 0 < 2 * (|b| + 1) by positivity)] at hlamUpper
        nlinarith
      rw [div_le_iff₀ (show 0 < 2 * lam by positivity)]
      have hbmul : -(|b| + 1) * (2 * lam) < b * (2 * lam) :=
        mul_lt_mul_of_pos_right hb (by positivity)
      have hnegcore : -Real.pi ^ 2 < -(|b| + 1) * (2 * lam) := by
        nlinarith
      exact (hnegcore.trans hbmul).le
  rw [nhdsWithin, Filter.tendsto_inf]
  constructor
  · exact Real.tendsto_exp_atBot.comp hdiv
  · rw [Filter.tendsto_principal]
    filter_upwards with lam
    exact Real.exp_pos _

end
end StatMech.FrontierD
