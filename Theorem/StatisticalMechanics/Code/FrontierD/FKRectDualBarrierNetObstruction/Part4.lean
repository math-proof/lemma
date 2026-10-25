/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualRankOneWinding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierNetObstruction.Part4
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDualBarrierNetObstructionHorizontalWalk_winding
    (R : FKRectTorus) :
    fkRectWalkWinding R
        (fkRectDualBarrierNetObstructionHorizontalWalk R) = (-1, 0) := by
  unfold fkRectDualBarrierNetObstructionHorizontalWalk
  rw [fkRectWalkWinding_copy,
    fkRectDualBarrierNetObstructionHorizontalAux_winding R R.width le_rfl]
  simp [ne_of_gt R.width_pos]

theorem fkRectDualBarrierNetObstructionVerticalWalk_winding
    (R : FKRectTorus) :
    fkRectWalkWinding R
        (fkRectDualBarrierNetObstructionVerticalWalk R) = (0, -1) := by
  unfold fkRectDualBarrierNetObstructionVerticalWalk
  rw [fkRectWalkWinding_copy,
    fkRectDualBarrierNetObstructionVerticalAux_winding R R.height le_rfl]
  simp [ne_of_gt R.height_pos]

end
end StatMech.FrontierD
