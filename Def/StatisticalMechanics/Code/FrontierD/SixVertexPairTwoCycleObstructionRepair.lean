/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoCycleMiddleFirst :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v := decide
    ((v.2.val = 0 /\ v.1.val ≠ 1) \/
      (v.2.val = 1 /\ v.1.val = 1))
  vertical v := decide
    ((v.2.val = 0 /\ v.1.val = 1) \/
      (v.2.val = 1 /\ v.1.val = 2))

def sixVertexFourByTwoCycleMiddleSecond :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v := decide
    ((v.2.val = 0 /\ v.1.val ≤ 2) \/
      (v.2.val = 1 /\ v.1.val = 3))
  vertical v := decide
    ((v.2.val = 0 /\ v.1.val = 3) \/
      (v.2.val = 1 /\ v.1.val = 0))

end
end StatMech.FrontierD
