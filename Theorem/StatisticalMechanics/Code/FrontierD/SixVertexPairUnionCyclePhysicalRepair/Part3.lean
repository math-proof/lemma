/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionCyclePhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWindingCycleBranchRecovery.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCyclePhysicalRepair.Part2


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexConfigurationPairUnionCyclePairedRepairs

theorem target_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt)
    (source) (branch) :
    sixVertexConfigurationPairTotalCPhysical
        (repairs.target source branch) =
      sixVertexConfigurationPairTotalCPhysical source := by
  have htotal := sixVertexPairAtMostTwoCycleFineRelated_totalC
    (repairs.related source branch)
  simpa [sixVertexConfigurationPairTotalCPhysical] using htotal.symm


end SixVertexConfigurationPairUnionCyclePairedRepairs
end
end StatMech.FrontierD
