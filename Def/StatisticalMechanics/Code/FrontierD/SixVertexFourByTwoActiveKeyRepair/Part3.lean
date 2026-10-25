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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoActiveCycleRepairSurplusToken :
    SixVertexHorizontalActualSurplusTokens sixVertexFourByTwoTorus
      sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoSectorZero
      sixVertexFourByTwoSectorTwo sixVertexFourByTwoSectorOne
      sixVertexFourByTwoSectorOne :=
  ⟨sixVertexFourByTwoActiveCycleRepairProfile,
    sixVertexFourByTwoActiveCycleRepairFiber,
    ⟨0, sixVertexFourByTwoActiveCycleRepairProfile_surplus_pos⟩⟩

end
end StatMech.FrontierD
