/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionMatchingNoGo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexPairSwitchMaskToTarget
    {T : EvenTorus}
    (source target : SixVertexArrows T × SixVertexArrows T) :
    SixVertexArrows T where
  horizontal v := decide
    (source.1.horizontal v ≠ target.1.horizontal v)
  vertical v := decide
    (source.1.vertical v ≠ target.1.vertical v)


end
end StatMech.FrontierD
