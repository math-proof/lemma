module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
public import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
public import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part5
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

theorem fkRectSquareCoverSide_gt_two (R : FKRectTorus) :
    2 < fkRectSquareCoverSide R := by
  exact lt_of_lt_of_le R.width_gt_two
    (Nat.le_mul_of_pos_right R.width R.height_pos)

end
end StatMech.FrontierD
