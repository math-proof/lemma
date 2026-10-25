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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCyclePhysicalRepair.Part3


namespace StatMech.FrontierD

noncomputable section

namespace SixVertexConfigurationPairUnionCyclePairedRepairs

theorem twoCycleFineHall
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexConfigurationPairTwoCycleFineHall T
      ⟨middle.val - 1, by omega⟩ middle
      ⟨middle.val + 1, by omega⟩ := by
  rw [configurationPairTwoCycleFineHall_iff_exists_injective]
  exact ⟨fun source => repairs.target source false,
    fun first second heq =>
      repairs.source_recoverable first second false heq,
    fun source => repairs.related source false⟩


theorem markedTraceCoefficientwiseLogConcave
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (repairs : SixVertexConfigurationPairUnionCyclePairedRepairs T middle
      hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val :=
  sixVertexMarkedTraceCoefficientwiseLogConcave_of_twoCycleFineHall
    T middle hmiddle_pos hmiddle_lt repairs.twoCycleFineHall

end SixVertexConfigurationPairUnionCyclePairedRepairs
end
end StatMech.FrontierD
