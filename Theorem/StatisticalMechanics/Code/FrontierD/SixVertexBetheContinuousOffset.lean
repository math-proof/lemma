/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffset.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexContinuousOffsetKernel_eq_thetaRightDerivative
    {c : Real} (hc : 2 < c) (x y : Real) :
    sixVertexContinuousOffsetKernel c x y =
      deriv (fun t => sixVertexTheta c x t) y := by
  rw [(hasDerivAt_sixVertexTheta_right hc x y).deriv]
  exact sixVertexRootDensityKernel_div_weight hc x y

theorem continuous_sixVertexContinuousOffsetSource
    {c : Real} (hc : 2 < c) :
    Continuous (sixVertexContinuousOffsetSource c) := by
  unfold sixVertexContinuousOffsetSource
  have htheta := continuous_sixVertexTheta hc
  exact ((htheta.comp
    (continuous_id.prodMk continuous_const)).add
      (htheta.comp (continuous_id.prodMk continuous_const))).div_const 2

theorem odd_sixVertexContinuousOffsetSource (c : Real) :
    Function.Odd (sixVertexContinuousOffsetSource c) := by
  intro x
  unfold sixVertexContinuousOffsetSource
  have hnegPi := sixVertexTheta_neg c x Real.pi
  have hpi := sixVertexTheta_neg c x (-Real.pi)
  simp only [neg_neg] at hpi
  rw [hnegPi, hpi]
  ring

theorem sixVertexRootDensityWeight_neg (c x : Real) :
    sixVertexRootDensityWeight c (-x) =
      sixVertexRootDensityWeight c x := by
  simp [sixVertexRootDensityWeight, sixVertexBetheIntegratingFactor,
    Real.cos_neg]


end
end StatMech.FrontierD
