/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair.Part5


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding :
    SixVertexHorizontalActualDeficitFineUnionKeyFiber
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoActiveObstructionMiddle_pos
        sixVertexFourByTwoActiveObstructionMiddle_lt
        sixVertexFourByTwoActiveObstructionGrade
        sixVertexFourByTwoActiveObstructionKey ↪
      SixVertexHorizontalActualSurplusFineUnionKeyFiber
        sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
        sixVertexFourByTwoActiveObstructionMiddle_pos
        sixVertexFourByTwoActiveObstructionMiddle_lt
        sixVertexFourByTwoActiveObstructionGrade
        sixVertexFourByTwoActiveCycleRepairKey where
  toFun _ := sixVertexFourByTwoActiveCycleRepairSurplusKeyFiber
  inj' := fun first second _ =>
    sixVertexFourByTwoActiveObstructionSourceKeyFiber_subsingleton first second

end
end StatMech.FrontierD
