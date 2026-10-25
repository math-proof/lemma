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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCyclePhysicalRepair.Part3


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexConfigurationPairUnionCyclePairedRepairs

noncomputable def family
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt)
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt) (branch : Bool) :
    SixVertexAtMostTwoCycleFamily T :=
  Classical.choose (repairs.related source branch).1

noncomputable def sign
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt)
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt) (branch : Bool) : Bool :=
  Classical.choose (Classical.choose_spec
    (repairs.related source branch).1)


noncomputable def signedTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt)
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt) (branch : Bool) :
    SixVertexSignedWindingCycleTarget
      (source.1.1, source.2.1) (repairs.family source branch)
      (repairs.sign source branch) where
  target := ((repairs.target source branch).1.1,
    (repairs.target source branch).2.1)
  horizontalDelta := (Classical.choose_spec (Classical.choose_spec
    (repairs.related source branch).1)).1
  verticalDelta := (Classical.choose_spec (Classical.choose_spec
    (repairs.related source branch).1)).2


def toPhysicalPairedBranches
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPhysicalPairedBranchEmbeddings T middle
      hmiddle_pos hmiddle_lt where
  branch choice :=
    { toFun := fun source => repairs.target source choice
      inj' := by
        intro first second heq
        exact repairs.source_recoverable first second choice heq }
  distinct := repairs.branch_distinct
  aggregateTotalC := by
    intro source
    change 2 * sixVertexConfigurationPairTotalCPhysical source ≤
      sixVertexConfigurationPairTotalCPhysical
          (repairs.target source false) +
        sixVertexConfigurationPairTotalCPhysical
          (repairs.target source true)
    rw [repairs.target_totalC source false,
      repairs.target_totalC source true]
    omega


end SixVertexConfigurationPairUnionCyclePairedRepairs
end
end StatMech.FrontierD
