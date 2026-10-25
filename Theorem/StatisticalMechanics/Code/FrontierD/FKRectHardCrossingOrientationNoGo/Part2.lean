/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHardCrossingOrientationNoGo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingAlgebra
import Def.StatisticalMechanics.Code.FrontierD.FKRectHardCrossingOrientationNoGo


namespace StatMech.FrontierD

theorem exists_wideCrossingScalarData_not_reverseOrientationBridge
    {q : Real} (hq : 1 <= q) :
    exists hard easy : Real,
      FKRectWideCrossingScalarData q hard easy /\
        ¬ FKRectWideCrossingReverseOrientationBridge q hard easy := by
  refine ⟨0, 1, fkRectWideCrossingScalarData_zero_one hq, ?_⟩
  unfold FKRectWideCrossingReverseOrientationBridge
  have hden : 0 < 1 + q ^ 2 := by positivity
  rw [not_le, div_pos_iff]
  exact Or.inl ⟨by norm_num, hden⟩


theorem FKRectWideCrossingScalarData.hard_ge_of_reverseOrientationBridge
    {q hard easy : Real} (hq : 1 <= q)
    (data : FKRectWideCrossingScalarData q hard easy)
    (hreverse : FKRectWideCrossingReverseOrientationBridge q hard easy) :
    1 / (8 * q ^ 2) <= hard := by
  exact crossing_hard_ge_one_div_eight_mul_pow_two hq data.hard_nonneg
    data.dualCover hreverse

end StatMech.FrontierD
