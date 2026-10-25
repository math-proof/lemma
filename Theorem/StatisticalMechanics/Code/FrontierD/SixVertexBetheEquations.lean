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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDelta_lt_neg_one {c : ℝ} (hc : 2 < c) :
    sixVertexDelta c < -1 := by
  unfold sixVertexDelta
  nlinarith


end
end StatMech.FrontierD
