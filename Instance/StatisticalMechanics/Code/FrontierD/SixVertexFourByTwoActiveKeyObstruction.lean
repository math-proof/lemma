/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction
open Finset


namespace StatMech.FrontierD

noncomputable section

section finiteChecks

instance sixVertexFourByTwoActiveIceRuleDecidable
    (omega : SixVertexArrows sixVertexFourByTwoTorus) :
    Decidable omega.IceRule :=
  inferInstanceAs (Decidable (forall v, omega.incomingCount v = 2))

end finiteChecks
end
end StatMech.FrontierD
