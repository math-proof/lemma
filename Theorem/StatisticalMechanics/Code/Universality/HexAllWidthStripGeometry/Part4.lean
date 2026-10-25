/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part5


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexAWPos_origin : hexAWPos hexAWOriginCoord = 0 := by
  simp [hexAWPos, hexAWOriginCoord]

@[simp] theorem hexAWMid_origin_zero :
    hexAWMid hexAWOriginCoord 0 = hexAWStart := by
  calc
    hexAWMid hexAWOriginCoord 0 =
        hexAWMid hexAWOriginCoord 0 - hexAWPos hexAWOriginCoord := by
      rw [hexAWPos_origin, sub_zero]
    _ = (1 / 2 : ℂ) * hexUnit (hexAWHeading hexAWOriginCoord 0) :=
      hexAWMid_sub_pos hexAWOriginCoord 0
    _ = hexAWStart := rfl


end
end StatMech.Universality
