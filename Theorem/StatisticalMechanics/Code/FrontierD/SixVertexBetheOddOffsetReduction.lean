/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeRatio_zero
    {c : Real} (hc : 0 < c) (k : Nat) :
    sixVertexFixedChargeRatio c 0 k = 1 := by
  unfold sixVertexFixedChargeRatio sixVertexLambdaAlongFour
  apply div_self
  exact (sixVertexLambda_isPerronFrobenius
    (sixVertexFourWidth 0 k) 0 (sixVertexFourWidth_even 0 k)
    (Nat.zero_le _) hc).1.ne'

theorem sixVertexFixedChargeLogRatio_zero
    {c : Real} (hc : 0 < c) (k : Nat) :
    sixVertexFixedChargeLogRatio c 0 k = 0 := by
  rw [sixVertexFixedChargeLogRatio, sixVertexFixedChargeRatio_zero hc,
    Real.log_one]


theorem sixVertexFixedChargeMatchesOffsetFourier_zero
    {c : Real} (hc : 0 < c) :
    SixVertexFixedChargeMatchesOffsetFourier c 0 := by
  simp [SixVertexFixedChargeMatchesOffsetFourier,
    sixVertexFixedChargeLogRatio_zero hc]


end
end StatMech.FrontierD
