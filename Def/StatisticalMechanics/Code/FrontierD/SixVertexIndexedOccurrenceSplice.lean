/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexIndexedOccurrenceSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11


namespace StatMech.FrontierD

noncomputable section

def fkIndexedOccurrenceLayerSwap (n : Nat) : Equiv.Perm (Bool × Fin n) where
  toFun x := (!x.1, x.2)
  invFun x := (!x.1, x.2)
  left_inv x := by rcases x with ⟨layer, i⟩; cases layer <;> rfl
  right_inv x := by rcases x with ⟨layer, i⟩; cases layer <;> rfl


def fkIndexedOccurrenceSlotEmbedding
    {T : EvenTorus} (n : Nat)
    (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer)) :
    (Bool × Fin n) ↪ FKLayeredStrandSlot T where
  toFun occurrence := (occurrence.1, key occurrence.1 occurrence.2)
  inj' := by
    rintro ⟨firstLayer, firstIndex⟩ ⟨secondLayer, secondIndex⟩ h
    have hlayer : firstLayer = secondLayer :=
      congrArg (fun slot : FKLayeredStrandSlot T => slot.1) h
    subst secondLayer
    have hindex : firstIndex = secondIndex := hinjective firstLayer
      (congrArg (fun slot : FKLayeredStrandSlot T => slot.2) h)
    rw [hindex]


noncomputable def fkIndexedOccurrenceSlotEquiv
    {T : EvenTorus} (n : Nat)
    (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer)) :
    FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T :=
  (fkIndexedOccurrenceLayerSwap n).viaFintypeEmbedding
    (fkIndexedOccurrenceSlotEmbedding n key hinjective)

end
end StatMech.FrontierD
