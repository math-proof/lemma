/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Def.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part2


namespace StatMech.Universality

open Complex HexWalk


namespace HexReturnCoord

theorem base_isUnit : base.IsUnit := by
  simp [IsUnit, base]


theorem isUnit_turn {d : HexReturnCoord} (hd : d.IsUnit) {t : ℤ}
    (ht : t = 1 ∨ t = -1) : (d.turn t).IsUnit := by
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl <;>
    simp [turn, left, right, IsUnit]

end HexReturnCoord
end StatMech.Universality
