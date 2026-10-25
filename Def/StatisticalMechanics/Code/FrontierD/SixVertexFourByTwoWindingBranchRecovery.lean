/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoWindingBranchRecovery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoObstructionWindingTarget :
    SixVertexSignedWindingCycleTarget
      (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)
      sixVertexFourByTwoBottomCycleFamily true where
  target := (sixVertexFourByTwoCycleMiddleFirst,
    sixVertexFourByTwoCycleMiddleSecond)
  horizontalDelta := by
    funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert
  verticalDelta := by
    funext v
    rcases v with ⟨x, y⟩
    fin_cases x <;> fin_cases y <;> decide +revert

end
end StatMech.FrontierD
