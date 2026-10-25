/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByTwoCycleMiddleFirst_ice :
    sixVertexFourByTwoCycleMiddleFirst.IceRule := by
  decide +revert

theorem sixVertexFourByTwoCycleMiddleSecond_ice :
    sixVertexFourByTwoCycleMiddleSecond.IceRule := by
  decide +revert

theorem sixVertexFourByTwoCycleMiddleFirst_seamCount :
    sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByTwoTorus
        sixVertexFourByTwoCycleMiddleFirst
        (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
  decide +revert

theorem sixVertexFourByTwoCycleMiddleSecond_seamCount :
    sixVertexUpCount
      (svTorusVerticalRows sixVertexFourByTwoTorus
        sixVertexFourByTwoCycleMiddleSecond
        (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
  decide +revert


end
end StatMech.FrontierD
