/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexIndexedOccurrenceSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
import Def.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkIndexedOccurrenceSlotEquiv_apply_key
    {T : EvenTorus} (n : Nat)
    (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (layer : Bool) (i : Fin n) :
    fkIndexedOccurrenceSlotEquiv n key hinjective (layer, key layer i) =
      (!layer, key (!layer) i) := by
  change fkIndexedOccurrenceSlotEquiv n key hinjective
      (fkIndexedOccurrenceSlotEmbedding n key hinjective (layer, i)) =
    fkIndexedOccurrenceSlotEmbedding n key hinjective (!layer, i)
  exact Equiv.Perm.viaFintypeEmbedding_apply_image _ _ _

theorem fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
    {T : EvenTorus} (n : Nat)
    (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (slot : FKLayeredStrandSlot T)
    (hslot : ¬ exists i : Fin n, key slot.1 i = slot.2) :
    fkIndexedOccurrenceSlotEquiv n key hinjective slot = slot := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨⟨layer, i⟩, h⟩
  have hlayer : layer = slot.1 := congrArg Prod.fst h
  subst layer
  exact hslot ⟨i, congrArg Prod.snd h⟩

@[simp] theorem fkIndexedOccurrenceSlotEquiv_apply_self
    {T : EvenTorus} (n : Nat)
    (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (slot : FKLayeredStrandSlot T) :
    fkIndexedOccurrenceSlotEquiv n key hinjective
        (fkIndexedOccurrenceSlotEquiv n key hinjective slot) = slot := by
  let embedding := fkIndexedOccurrenceSlotEmbedding n key hinjective
  by_cases hslot : slot ∈ Set.range embedding
  · obtain ⟨⟨layer, i⟩, rfl⟩ := hslot
    change ((fkIndexedOccurrenceLayerSwap n).viaFintypeEmbedding embedding)
        (((fkIndexedOccurrenceLayerSwap n).viaFintypeEmbedding embedding)
          (embedding (layer, i))) = embedding (layer, i)
    rw [Equiv.Perm.viaFintypeEmbedding_apply_image,
      Equiv.Perm.viaFintypeEmbedding_apply_image]
    cases layer <;> rfl
  · change ((fkIndexedOccurrenceLayerSwap n).viaFintypeEmbedding embedding)
        (((fkIndexedOccurrenceLayerSwap n).viaFintypeEmbedding embedding)
          slot) = slot
    have hfix := Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
      (fkIndexedOccurrenceLayerSwap n) embedding hslot
    rw [hfix, hfix]


end
end StatMech.FrontierD
