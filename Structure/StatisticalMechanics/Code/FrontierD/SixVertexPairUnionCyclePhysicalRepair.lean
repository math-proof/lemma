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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCyclePhysicalRepair.Part2


namespace StatMech.FrontierD

noncomputable section

structure SixVertexConfigurationPairUnionCyclePairedRepairs
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) where
  target : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt → Bool →
    SixVertexConfigurationPhysicalTarget T middle
  related : ∀ source branch,
    sixVertexPairAtMostTwoCycleFineRelated
      (source.1.1, source.2.1)
      ((target source branch).1.1, (target source branch).2.1)
  source_recoverable : ∀ first second branch,
    target first branch = target second branch → first = second
  branch_distinct : ∀ source,
    target source false ≠ target source true


structure SixVertexConfigurationPairUnionCycleOffDiagonalEmbedding
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) where
  target : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt ↪
    SixVertexConfigurationPhysicalTarget T middle
  related : ∀ source,
    sixVertexPairAtMostTwoCycleFineRelated
      (source.1.1, source.2.1)
      ((target source).1.1, (target source).2.1)
  layers_ne : ∀ source, (target source).1 ≠ (target source).2

end
end StatMech.FrontierD
