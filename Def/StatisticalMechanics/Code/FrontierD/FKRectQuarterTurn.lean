/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectQuarterTurnTorus (R : FKRectTorus) (hheight : 4 < R.height) :
    FKRectTorus where
  width := R.height / 2
  height := 2 * R.width
  width_gt_two := by
    have hH := Nat.two_mul_div_two_of_even R.height_even
    omega
  height_gt_two := by
    have hW := R.width_gt_two
    omega
  height_even := even_two_mul R.width

end
end StatMech.FrontierD
