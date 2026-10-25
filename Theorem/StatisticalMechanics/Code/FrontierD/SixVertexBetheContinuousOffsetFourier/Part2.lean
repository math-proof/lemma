/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part2


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

theorem continuous_sixVertexOffsetRapidityProfile
    {lam : Real} (hlam : 0 < lam) :
    Continuous (sixVertexOffsetRapidityProfile lam) := by
  unfold sixVertexOffsetRapidityProfile
  apply Continuous.add (by fun_prop)
  apply continuous_tsum
  · intro n
    unfold sixVertexOffsetCorrectionTerm
    fun_prop
  · have hq0 : 0 <= Real.exp (-2 * lam) := Real.exp_pos _ |>.le
    have hq1 : Real.exp (-2 * lam) < 1 := by
      rw [<- Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    exact ((summable_geometric_of_lt_one hq0 hq1).comp_injective
      Nat.succ_injective).mul_left (2 / Real.pi)
  · intro n alpha
    exact norm_sixVertexOffsetCorrectionTerm_le lam n alpha

theorem odd_sixVertexOffsetCorrectionTerm (lam : Real) (n : Nat) :
    Function.Odd (sixVertexOffsetCorrectionTerm lam n) := by
  intro alpha
  unfold sixVertexOffsetCorrectionTerm
  rw [mul_neg, Real.sin_neg]
  ring

theorem odd_sixVertexOffsetRapidityProfile (lam : Real) :
    Function.Odd (sixVertexOffsetRapidityProfile lam) := by
  intro alpha
  unfold sixVertexOffsetRapidityProfile
  have hsum :
      (∑' n : Nat, sixVertexOffsetCorrectionTerm lam n (-alpha)) =
        -(∑' n : Nat, sixVertexOffsetCorrectionTerm lam n alpha) := by
    rw [<- tsum_neg]
    apply tsum_congr
    intro n
    exact odd_sixVertexOffsetCorrectionTerm lam n alpha
  rw [hsum]
  ring


end
end StatMech.FrontierD
