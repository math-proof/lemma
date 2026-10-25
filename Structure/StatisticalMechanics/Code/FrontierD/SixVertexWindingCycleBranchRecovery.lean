/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation


namespace StatMech.FrontierD

noncomputable section

structure SixVertexSignedWindingCycleTarget
    {T : EvenTorus} (source : SixVertexArrows T × SixVertexArrows T)
    (family : SixVertexAtMostTwoCycleFamily T) (sign : Bool) where
  target : SixVertexArrows T × SixVertexArrows T
  horizontalDelta :
    sixVertexPairUnionHorizontalDelta source target =
      fun v => if sign then family.horizontalFlow v
        else -family.horizontalFlow v
  verticalDelta :
    sixVertexPairUnionVerticalDelta source target =
      fun v => if sign then family.verticalFlow v
        else -family.verticalFlow v

end
end StatMech.FrontierD
