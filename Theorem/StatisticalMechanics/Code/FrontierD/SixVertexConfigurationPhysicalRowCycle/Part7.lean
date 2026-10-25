/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexPhysicalSourceEquivRowCycles_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt) :
    sixVertexPhysicalRowCyclePairTotalC
        (sixVertexPhysicalSourceEquivRowCycles source) =
      sixVertexConfigurationPairTotalCPhysical source := by
  simp [sixVertexPhysicalRowCyclePairTotalC,
    sixVertexMarkedSectorRowCyclePairTotalC,
    sixVertexConfigurationPairTotalCPhysical,
    sixVertexPhysicalSourceEquivRowCycles,
    sixVertexTorusCTypeCount_eq_rowCycleTotalC]

theorem sixVertexPhysicalTargetEquivRowCycles_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexConfigurationPhysicalTarget T middle) :
    sixVertexPhysicalRowCyclePairTotalC
        (sixVertexPhysicalTargetEquivRowCycles target) =
      sixVertexConfigurationPairTotalCPhysical target := by
  simp [sixVertexPhysicalRowCyclePairTotalC,
    sixVertexMarkedSectorRowCyclePairTotalC,
    sixVertexConfigurationPairTotalCPhysical,
    sixVertexPhysicalTargetEquivRowCycles,
    sixVertexTorusCTypeCount_eq_rowCycleTotalC]

@[simp] theorem sixVertexPhysicalTargetEquivRowCycles_symm_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexPhysicalRowCycleTarget T middle) :
    sixVertexConfigurationPairTotalCPhysical
        (sixVertexPhysicalTargetEquivRowCycles.symm target) =
      sixVertexPhysicalRowCyclePairTotalC target := by
  have h := sixVertexPhysicalTargetEquivRowCycles_totalC
    (sixVertexPhysicalTargetEquivRowCycles.symm target)
  simpa using h.symm


end
end StatMech.FrontierD
