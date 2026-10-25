/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4
import Mathlib.Topology.MetricSpace.Antilipschitz
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexRapidityMomentumDerivativeFloor_pos
    {lam : Real} (hlam : 0 < lam) :
    0 < sixVertexRapidityMomentumDerivativeFloor lam := by
  unfold sixVertexRapidityMomentumDerivativeFloor
  exact div_pos (Real.sinh_pos_iff.mpr hlam) (by positivity)

theorem sixVertexRapidityMomentumDerivativeFloor_le
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    sixVertexRapidityMomentumDerivativeFloor lam <=
      sixVertexXiFourier lam alpha := by
  rw [sixVertexXiFourier_eq hlam]
  unfold sixVertexRapidityMomentumDerivativeFloor
  have hsinh : 0 < Real.sinh lam := Real.sinh_pos_iff.mpr hlam
  have hden : 0 < Real.cosh lam - Real.cos alpha := by
    have hc : 1 < Real.cosh lam := Real.one_lt_cosh.mpr hlam.ne'
    linarith [Real.cos_le_one alpha]
  have hupper : Real.cosh lam - Real.cos alpha <= Real.cosh lam + 1 := by
    linarith [Real.neg_one_le_cos alpha]
  exact div_le_div_of_nonneg_left hsinh.le hden hupper

end
end StatMech.FrontierD
