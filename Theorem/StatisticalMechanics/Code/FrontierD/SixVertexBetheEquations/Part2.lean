/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part12
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexThetaDenominator_pos {c : ℝ} (hc : 2 < c) (x y : ℝ) :
    0 < sixVertexThetaDenominator c x y := by
  have hx := Real.neg_one_le_cos x
  have hy := Real.neg_one_le_cos y
  have hdelta := sixVertexDelta_lt_neg_one hc
  unfold sixVertexThetaDenominator
  linarith


end
end StatMech.FrontierD
