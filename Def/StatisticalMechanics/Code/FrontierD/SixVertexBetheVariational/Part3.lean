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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexThetaFDeriv (c x y : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      (4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
        sixVertexThetaDerivativeDenominator c x y) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
        sixVertexThetaDerivativeDenominator c x y)

end
end StatMech.FrontierD
