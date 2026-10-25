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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part6
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexBethePairOneForm (c : ℝ) (xy : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      (sixVertexNormalizedTheta c xy.1 xy.2) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (sixVertexNormalizedTheta c xy.2 xy.1)

end
end StatMech.FrontierD
