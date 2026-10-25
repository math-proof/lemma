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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheIntegratingFactor_pos {c : ℝ} (hc : 2 < c) (x : ℝ) :
    0 < sixVertexBetheIntegratingFactor c x := by
  have hdelta := sixVertexDelta_lt_neg_one hc
  have hcos := Real.neg_one_le_cos x
  unfold sixVertexBetheIntegratingFactor
  linarith


end
end StatMech.FrontierD
