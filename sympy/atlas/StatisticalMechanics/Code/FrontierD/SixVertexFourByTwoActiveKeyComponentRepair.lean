/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyComponentRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair








namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoActiveObstructionCycleRepairComponents :
    SixVertexHorizontalTwoCycleFiberReconnectionComponents
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveObstructionKey
      sixVertexFourByTwoActiveCycleRepairKey :=
  sixVertexHorizontalTwoCycleFiberReconnectionComponentsOfEmbedding
    sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding

theorem sixVertexFourByTwoActiveObstructionCycleRepairComponents_supported :
    SixVertexPairFineUnionKeyTwoCycleRelated
      sixVertexFourByTwoActiveObstructionKey
      sixVertexFourByTwoActiveCycleRepairKey :=
  sixVertexFourByTwoActiveObstructionKey_cycleRepair_related

theorem sixVertexFourByTwoActiveObstructionCycleRepairComponents_reconnect
    (source : SixVertexHorizontalActualDeficitFineUnionKeyFiber
      sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne
      sixVertexFourByTwoActiveObstructionMiddle_pos
      sixVertexFourByTwoActiveObstructionMiddle_lt
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveObstructionKey) :
    sixVertexFourByTwoActiveObstructionCycleRepairComponents.reconnect source =
      sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding source :=
  rfl

theorem sixVertexFourByTwoActiveObstructionCycleRepairComponents_embedding :
    sixVertexFourByTwoActiveObstructionCycleRepairComponents.toEmbedding =
      sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding := by
  rfl

end

end StatMech.FrontierD
