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
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCyclePhysicalRepair


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexConfigurationPairUnionCycleOffDiagonalEmbedding

def toPairedRepairs
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (embedding : SixVertexConfigurationPairUnionCycleOffDiagonalEmbedding
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt where
  target source branch :=
    if branch then sixVertexSwapPhysicalTarget (embedding.target source)
    else embedding.target source
  related source branch := by
    cases branch
    · simpa using embedding.related source
    · simpa [sixVertexSwapPhysicalTarget] using
        sixVertexPairAtMostTwoCycleFineRelated_swap_target
          (embedding.related source)
  source_recoverable := by
    intro first second branch heq
    cases branch
    · exact embedding.target.injective heq
    · apply embedding.target.injective
      exact sixVertexSwapPhysicalTarget_injective heq
  branch_distinct := by
    intro source heq
    apply embedding.layers_ne source
    exact congrArg Prod.fst heq

end SixVertexConfigurationPairUnionCycleOffDiagonalEmbedding
end
end StatMech.FrontierD
