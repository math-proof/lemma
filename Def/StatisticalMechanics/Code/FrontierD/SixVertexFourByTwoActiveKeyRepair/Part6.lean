module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
