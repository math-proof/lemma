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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part8
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexPhysicalRowCycleOffDiagonalGradeEquiv
    {T : EvenTorus} {middle : Fin (T.width + 1)} (totalC : Nat) :
    {target : SixVertexPhysicalRowCycleOffDiagonalTarget T middle //
      sixVertexPhysicalRowCyclePairTotalC target.1 = totalC} ≃
      {target :
          {pair : SixVertexPhysicalRowCycleTarget T middle //
            sixVertexPhysicalRowCyclePairTotalC pair = totalC} //
        target.1.1 ≠ target.1.2} where
  toFun target := ⟨⟨target.1.1, target.2⟩, target.1.2⟩
  invFun target := ⟨⟨target.1.1, target.2⟩, target.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def sixVertexPhysicalRowCycleDiagonalGradeEquiv
    {T : EvenTorus} {middle : Fin (T.width + 1)} (totalC : Nat) :
    {target :
        {pair : SixVertexPhysicalRowCycleTarget T middle //
          sixVertexPhysicalRowCyclePairTotalC pair = totalC} //
      target.1.1 = target.1.2} ≃
      {rows : SixVertexMarkedSectorRowCycle T middle //
        2 * sixVertexMarkedSectorRowCycleTotalC rows = totalC} where
  toFun target := ⟨target.1.1.1, by
    have hgrade := target.1.2
    change sixVertexMarkedSectorRowCycleTotalC target.1.1.1 +
      sixVertexMarkedSectorRowCycleTotalC target.1.1.2 = totalC at hgrade
    rw [← target.2] at hgrade
    simpa [two_mul] using hgrade⟩
  invFun rows := ⟨⟨(rows.1, rows.1), by
    simpa [sixVertexPhysicalRowCyclePairTotalC,
      sixVertexMarkedSectorRowCyclePairTotalC, two_mul] using rows.2⟩, rfl⟩
  left_inv target := by
    rcases target with ⟨⟨⟨first, second⟩, hgrade⟩, heq⟩
    change first = second at heq
    subst second
    rfl
  right_inv rows := by
    apply Subtype.ext
    rfl

end
end StatMech.FrontierD
