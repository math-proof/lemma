/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2


namespace StatMech.FrontierD

noncomputable section

instance sixVertexTwoCycleRepairIceRuleDecidable
    {T : EvenTorus} (omega : SixVertexArrows T) :
    Decidable omega.IceRule :=
  inferInstanceAs (Decidable (forall v, omega.incomingCount v = 2))

end
end StatMech.FrontierD
