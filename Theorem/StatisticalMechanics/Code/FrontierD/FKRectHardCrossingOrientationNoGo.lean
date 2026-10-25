/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHardCrossingOrientationNoGo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingAlgebra
import Structure.StatisticalMechanics.Code.FrontierD.FKRectHardCrossingOrientationNoGo


namespace StatMech.FrontierD

theorem FKRectWideCrossingScalarData.easy_ge_one_div_eight_mul_pow_six
    {q hard easy : Real} (hq : 1 <= q)
    (data : FKRectWideCrossingScalarData q hard easy) :
    1 / (8 * q ^ 6) <= easy :=
  crossing_vertical_ge_one_div_eight_mul_pow_six hq data.easy_nonneg
    data.dualCover data.sameOrientationQuadratic


theorem fkRectWideCrossingScalarData_zero_one
    {q : Real} (hq : 1 <= q) :
    FKRectWideCrossingScalarData q 0 1 := by
  constructor
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · have hden : 0 < 1 + q := by linarith
    rw [div_le_one hden]
    linarith
  · norm_num
  · norm_num


theorem not_exists_positive_hardFloor_of_wideCrossingScalarData
    {q : Real} (hq : 1 <= q) :
    ¬ (exists floor : Real, 0 < floor /\
      forall hard easy : Real,
        FKRectWideCrossingScalarData q hard easy -> floor <= hard) := by
  rintro ⟨floor, hfloor, hall⟩
  have hle := hall 0 1 (fkRectWideCrossingScalarData_zero_one hq)
  linarith


end StatMech.FrontierD
