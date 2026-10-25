/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredVertexCrossFineRowProfile
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredFullComponentSwap.Part2


namespace StatMech.FrontierD

noncomputable section

def fkColoredFullSwapLayeredSlotEquiv
    {T : EvenTorus} (mask : T.Vertex -> Bool) :
    FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T where
  toFun slot := (if mask slot.2.1 then !slot.1 else slot.1, slot.2)
  invFun slot := (if mask slot.2.1 then !slot.1 else slot.1, slot.2)
  left_inv slot := by
    rcases slot with ⟨layer, v, side⟩
    by_cases hm : mask v <;> cases layer <;> simp [hm]
  right_inv slot := by
    rcases slot with ⟨layer, v, side⟩
    by_cases hm : mask v <;> cases layer <;> simp [hm]

end
end StatMech.FrontierD
