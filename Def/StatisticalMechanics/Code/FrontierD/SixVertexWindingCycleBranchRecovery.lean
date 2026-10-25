/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexSignedWindingCycleTarget

def swapTarget
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T} {sign : Bool}
    (branch : SixVertexSignedWindingCycleTarget source family sign) :
    SixVertexSignedWindingCycleTarget source family sign where
  target := (branch.target.2, branch.target.1)
  horizontalDelta := by
    rw [← branch.horizontalDelta]
    funext v
    unfold sixVertexPairUnionHorizontalDelta sixVertexPairUnionHorizontal
    simp only [Prod.fst, Prod.snd]
    omega
  verticalDelta := by
    rw [← branch.verticalDelta]
    funext v
    unfold sixVertexPairUnionVerticalDelta sixVertexPairUnionVertical
    simp only [Prod.fst, Prod.snd]
    omega

end SixVertexSignedWindingCycleTarget
end
end StatMech.FrontierD
