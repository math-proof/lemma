/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap


namespace StatMech.FrontierD

noncomputable section

def fkColoredLayeredStrandSlotSwapLayers
    {T : EvenTorus} : Equiv.Perm (FKLayeredStrandSlot T) where
  toFun slot := (!slot.1, slot.2)
  invFun slot := (!slot.1, slot.2)
  left_inv slot := by rcases slot with ⟨layer, slot⟩; cases layer <;> rfl
  right_inv slot := by rcases slot with ⟨layer, slot⟩; cases layer <;> rfl

end
end StatMech.FrontierD
