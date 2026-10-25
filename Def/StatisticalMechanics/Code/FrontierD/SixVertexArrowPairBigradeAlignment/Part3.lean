/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexArrowPairBigradeAlignment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexArrowPairBigradeAlignment.Part2


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexArrowPairTrueStrandSlotEquivSum
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    {slot : FKLayeredStrandSlot T //
        sixVertexArrowPairStrandSlotColor omega eta slot = true} ≃
      {slot : T.Vertex × Bool //
          sixVertexArrowStrandSlotColor omega slot = true} ⊕
        {slot : T.Vertex × Bool //
          sixVertexArrowStrandSlotColor eta slot = true} where
  toFun slot := by
    rcases slot with ⟨⟨layer, v, side⟩, hcolor⟩
    cases layer
    · exact Sum.inl ⟨(v, side), hcolor⟩
    · exact Sum.inr ⟨(v, side), hcolor⟩
  invFun slot := by
    rcases slot with slot | slot
    · exact ⟨(false, slot.1.1, slot.1.2), slot.2⟩
    · exact ⟨(true, slot.1.1, slot.1.2), slot.2⟩
  left_inv slot := by
    rcases slot with ⟨⟨layer, v, side⟩, hcolor⟩
    cases layer <;> rfl
  right_inv slot := by
    rcases slot with slot | slot <;> rfl

end
end StatMech.FrontierD
