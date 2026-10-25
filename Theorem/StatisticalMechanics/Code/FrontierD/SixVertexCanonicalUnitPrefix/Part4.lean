/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoStrandSplit
import Def.StatisticalMechanics.Code.FrontierD.SixVertexCanonicalUnitPrefix.Part3


namespace StatMech.FrontierD

theorem sixVertexCanonicalUnitItemPrefix_sum
    {Item : Type*} (items : List Item) (step : Item -> Int)
    (hsteps : ∀ item ∈ items,
      step item = 0 \/ step item = 1 \/ step item = -1)
    (hsum : (items.map step).sum = 2) :
    (((items.take (sixVertexCanonicalUnitItemPrefixLength
      items step hsteps hsum)).map step).sum) = 1 :=
  (Nat.find_spec
    (exists_item_prefix_length_sum_eq_one items step hsteps hsum)).2

theorem sixVertexCanonicalUnitItemSuffix_sum
    {Item : Type*} (items : List Item) (step : Item -> Int)
    (hsteps : ∀ item ∈ items,
      step item = 0 \/ step item = 1 \/ step item = -1)
    (hsum : (items.map step).sum = 2) :
    (((items.drop (sixVertexCanonicalUnitItemPrefixLength
      items step hsteps hsum)).map step).sum) = 1 := by
  have hsplit := List.take_append_drop
    (sixVertexCanonicalUnitItemPrefixLength items step hsteps hsum) items
  have hprefix := sixVertexCanonicalUnitItemPrefix_sum
    items step hsteps hsum
  rw [← hsplit, List.map_append, List.sum_append, hprefix] at hsum
  omega

theorem sixVertexCanonicalUnitItemPrefix_ne_nil
    {Item : Type*} (items : List Item) (step : Item -> Int)
    (hsteps : ∀ item ∈ items,
      step item = 0 \/ step item = 1 \/ step item = -1)
    (hsum : (items.map step).sum = 2) :
    items.take (sixVertexCanonicalUnitItemPrefixLength
      items step hsteps hsum) ≠ [] := by
  intro hnil
  have hprefix := sixVertexCanonicalUnitItemPrefix_sum
    items step hsteps hsum
  rw [hnil] at hprefix
  simp at hprefix

theorem sixVertexCanonicalUnitItemSuffix_ne_nil
    {Item : Type*} (items : List Item) (step : Item -> Int)
    (hsteps : ∀ item ∈ items,
      step item = 0 \/ step item = 1 \/ step item = -1)
    (hsum : (items.map step).sum = 2) :
    items.drop (sixVertexCanonicalUnitItemPrefixLength
      items step hsteps hsum) ≠ [] := by
  intro hnil
  have hsuffix := sixVertexCanonicalUnitItemSuffix_sum
    items step hsteps hsum
  rw [hnil] at hsuffix
  simp at hsuffix

end StatMech.FrontierD
