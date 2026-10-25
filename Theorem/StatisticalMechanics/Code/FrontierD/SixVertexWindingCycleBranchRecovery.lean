/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWindingCycleBranchRecovery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
import Def.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexSignedWindingCycleTarget

@[simp] theorem swapTarget_target
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T} {sign : Bool}
    (branch : SixVertexSignedWindingCycleTarget source family sign) :
    branch.swapTarget.target = (branch.target.2, branch.target.1) := rfl


theorem target_ne_swapTarget_iff
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T} {sign : Bool}
    (branch : SixVertexSignedWindingCycleTarget source family sign) :
    branch.target ≠ branch.swapTarget.target ↔
      branch.target.1 ≠ branch.target.2 := by
  constructor
  · intro hne heq
    apply hne
    apply Prod.ext <;> simpa [heq]
  · intro hne heq
    exact hne (congrArg Prod.fst heq)


theorem related
    {T : EvenTorus} {source : SixVertexArrows T × SixVertexArrows T}
    {family : SixVertexAtMostTwoCycleFamily T} {sign : Bool}
    (branch : SixVertexSignedWindingCycleTarget source family sign) :
    sixVertexPairAtMostTwoCycleRelated source branch.target :=
  ⟨family, sign, branch.horizontalDelta, branch.verticalDelta⟩


end SixVertexSignedWindingCycleTarget
end
end StatMech.FrontierD
