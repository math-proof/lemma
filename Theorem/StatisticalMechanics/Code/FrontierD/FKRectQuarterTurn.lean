/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectQuarterTurnTorus_width
    (R : FKRectTorus) (hheight : 4 < R.height) :
    (fkRectQuarterTurnTorus R hheight).width = R.height / 2 := rfl

@[simp] theorem fkRectQuarterTurnTorus_height
    (R : FKRectTorus) (hheight : 4 < R.height) :
    (fkRectQuarterTurnTorus R hheight).height = 2 * R.width := rfl

theorem fkRectHeight_two_mul_div_two (R : FKRectTorus) :
    2 * (R.height / 2) = R.height := by
  exact Nat.two_mul_div_two_of_even R.height_even


end
end StatMech.FrontierD
