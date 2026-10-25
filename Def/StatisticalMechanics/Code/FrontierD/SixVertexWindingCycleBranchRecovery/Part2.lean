/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexSignedWindingCycleTarget

def recover
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T} {sign : Bool}
    (branch : SixVertexSignedWindingCycleTarget source family sign) :
    SixVertexSignedWindingCycleTarget branch.target family (!sign) where
  target := source
  horizontalDelta := by
    funext v
    have h := congrFun branch.horizontalDelta v
    unfold sixVertexPairUnionHorizontalDelta at h ⊢
    cases sign <;> simp at h ⊢ <;> omega
  verticalDelta := by
    funext v
    have h := congrFun branch.verticalDelta v
    unfold sixVertexPairUnionVerticalDelta at h ⊢
    cases sign <;> simp at h ⊢ <;> omega

end SixVertexSignedWindingCycleTarget
end
end StatMech.FrontierD
