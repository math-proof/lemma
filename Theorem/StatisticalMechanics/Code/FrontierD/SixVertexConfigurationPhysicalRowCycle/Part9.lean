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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part10
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexPhysicalRowCycleOffDiagonalGradeFiber
    (T : EvenTorus) (middle : Fin (T.width + 1)) (totalC : Nat) :
    Fintype.card
        {target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle //
          sixVertexPhysicalRowCyclePairTotalC target.1 = totalC} =
      sixVertexMarkedSectorRowCyclePairGradeCount
          T middle middle totalC -
        sixVertexMarkedSectorRowCycleDiagonalGradeCount
          T middle totalC := by
  rw [Fintype.card_congr
    (sixVertexPhysicalRowCycleOffDiagonalGradeEquiv totalC)]
  rw [Fintype.card_subtype_compl]
  have hpair :
      Nat.card
          {pair : SixVertexPhysicalRowCycleTarget T middle //
            sixVertexPhysicalRowCyclePairTotalC pair = totalC} =
        sixVertexMarkedSectorRowCyclePairGradeCount
          T middle middle totalC := by
    change Nat.card
        {pair : SixVertexMarkedSectorRowCycle T middle ×
            SixVertexMarkedSectorRowCycle T middle //
          sixVertexMarkedSectorRowCyclePairTotalC pair = totalC} = _
    rw [Nat.card_eq_fintype_card]
    exact card_sixVertexMarkedSectorRowCyclePairGradeFiber
      T middle middle totalC
  have hdiagonal :
      Nat.card
          {target :
              {pair : SixVertexPhysicalRowCycleTarget T middle //
                sixVertexPhysicalRowCyclePairTotalC pair = totalC} //
            target.1.1 = target.1.2} =
        sixVertexMarkedSectorRowCycleDiagonalGradeCount
          T middle totalC := by
    rw [Nat.card_congr
      (sixVertexPhysicalRowCycleDiagonalGradeEquiv totalC)]
    rw [Nat.card_eq_fintype_card]
    exact card_sixVertexMarkedSectorRowCycleDiagonalGradeFiber
      T middle totalC
  simpa only [← Nat.card_eq_fintype_card] using
    congrArg₂ Nat.sub hpair hdiagonal

@[simp] theorem sixVertexPhysicalRowCycleOffDiagonalSwap_totalC
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    (target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle) :
    sixVertexPhysicalRowCyclePairTotalC
        (sixVertexPhysicalRowCycleOffDiagonalSwap target) =
      sixVertexPhysicalRowCyclePairTotalC target.1 := by
  simp [sixVertexPhysicalRowCyclePairTotalC,
    sixVertexMarkedSectorRowCyclePairTotalC,
    sixVertexPhysicalRowCycleOffDiagonalSwap, Nat.add_comm]


end
end StatMech.FrontierD
