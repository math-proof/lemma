/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualRankOneWinding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierNetObstruction.Part5
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDualBarrierNetObstruction_hasNet (R : FKRectTorus) :
    FKRectHasNet R (fkRectDualBarrierNetObstructionConfiguration R) := by
  apply FKRectHasNet.of_connected_closedWalks R
    (fkRectDualBarrierNetObstructionConfiguration R)
    (fkRectDualBarrierNetObstructionConnectionWalk R).reachable
    (fkRectDualBarrierNetObstructionHorizontalWalk R)
    (fkRectDualBarrierNetObstructionVerticalWalk R)
  rw [fkRectDualBarrierNetObstructionHorizontalWalk_winding,
    fkRectDualBarrierNetObstructionVerticalWalk_winding]
  norm_num [FKRectWindingIndependent]


theorem fkRectDualBarrierNetObstruction_hasNet_and_dualNoCrossing
    (R : FKRectTorus) :
    FKRectHasNet R (fkRectDualBarrierNetObstructionConfiguration R) ∧
      fkRectDualBarrierNetObstructionConfiguration R ∈
        fkRectDualPreimageEvent R
          (fkRectNoLeftStripCrossingEvent R 1) := by
  exact ⟨fkRectDualBarrierNetObstruction_hasNet R,
    (fkRectDualBarrierNetObstruction_dual_mem_source R).1⟩

end
end StatMech.FrontierD
