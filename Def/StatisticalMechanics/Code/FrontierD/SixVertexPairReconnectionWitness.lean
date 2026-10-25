/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairReconnectionWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexPairReconnectionWitness
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoMiddleArrows :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v := decide
    ((v.2.val = 0 /\ v.1.val = 3) \/
      (v.2.val = 1 /\ v.1.val ≠ 3))
  vertical v := decide
    ((v.2.val = 0 /\ v.1.val = 0) \/
      (v.2.val = 1 /\ v.1.val = 3))

end
end StatMech.FrontierD
