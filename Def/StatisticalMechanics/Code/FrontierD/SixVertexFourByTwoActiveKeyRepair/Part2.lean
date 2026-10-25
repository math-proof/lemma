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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoActiveCycleRepairProfile :
    SixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus :=
  sixVertexHorizontalPairCompletionProfile sixVertexFourByTwoTorus
    (sixVertexFourByTwoCycleMiddleFirst.horizontal,
      sixVertexFourByTwoCycleMiddleSecond.horizontal)

def sixVertexFourByTwoActiveCycleRepairFiber :
    SixVertexHorizontalPairProfileFiber sixVertexFourByTwoTorus
      sixVertexFourByTwoActiveObstructionGrade
      sixVertexFourByTwoActiveCycleRepairProfile :=
  ⟨⟨(sixVertexFourByTwoCycleMiddleFirst.horizontal,
      sixVertexFourByTwoCycleMiddleSecond.horizontal),
    sixVertexFourByTwoActiveCycleRepair_bigrade⟩, rfl⟩


end
end StatMech.FrontierD
