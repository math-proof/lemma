/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyComponentRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair.Part6


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

end
end StatMech.FrontierD
