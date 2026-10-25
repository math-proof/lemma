/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexThetaDerivativeDenominator_swap (c x y : ℝ) :
    sixVertexThetaDerivativeDenominator c y x =
      sixVertexThetaDerivativeDenominator c x y := by
  unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
  ring

theorem sixVertexThetaDerivativeDenominator_pos {c : ℝ} (hc : 2 < c)
    (x y : ℝ) : 0 < sixVertexThetaDerivativeDenominator c x y := by
  unfold sixVertexThetaDerivativeDenominator
  have hden := sixVertexThetaDenominator_pos hc x y
  positivity


theorem hasDerivAt_sixVertexTheta_right {c : ℝ} (hc : 2 < c)
    (x y : ℝ) :
    HasDerivAt (fun t => sixVertexTheta c x t)
      (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
        sixVertexThetaDerivativeDenominator c x y) y := by
  have hleft := (hasDerivAt_sixVertexTheta_left hc y x).neg
  have hfun : (-(fun t => sixVertexTheta c t x)) =
      fun t => sixVertexTheta c x t := by
    funext t
    exact (sixVertexTheta_antisymm c t x).symm
  rw [hfun] at hleft
  convert hleft using 1
  unfold sixVertexBetheIntegratingFactor
    sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
  ring


end
end StatMech.FrontierD
