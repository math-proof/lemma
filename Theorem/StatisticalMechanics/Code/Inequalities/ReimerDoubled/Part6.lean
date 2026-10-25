/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


theorem downLeft_eq_self (i : α) {𝒜 : Finset (Finset (α ⊕ α))} (h : IsDownAtLeft i 𝒜) :
    downLeft i 𝒜 = 𝒜 := by
  unfold downLeft
  ext s
  rw [Down.mem_compression]
  constructor
  · rintro (⟨hs, _⟩ | ⟨hns, hins⟩)
    · exact hs
    · by_cases hi : Sum.inl i ∈ s
      · rw [insert_eq_of_mem hi] at hins; exact absurd hins hns
      · have := h _ hins; rw [erase_insert hi] at this; exact absurd this hns
  · intro hs; exact Or.inl ⟨hs, h _ hs⟩


theorem upRight_eq_self (i : α) {𝒜 : Finset (Finset (α ⊕ α))} (h : IsUpAtRight i 𝒜) :
    upRight i 𝒜 = 𝒜 := by
  unfold upRight upComp
  ext s
  rw [UV.mem_compression]
  constructor
  · rintro (⟨hs, _⟩ | ⟨hns, b, hb, hbs⟩)
    · exact hs
    · 
      by_cases hi : Sum.inr i ∈ b
      · 
        have : UV.compress ({Sum.inr i} : Finset (α ⊕ α)) ∅ b = b := by
          rw [UV.compress]; simp [Finset.disjoint_singleton_left, hi]
        rw [this] at hbs; rw [← hbs] at hns; exact absurd hb hns
      · 
        have hc : UV.compress ({Sum.inr i} : Finset (α ⊕ α)) ∅ b = insert (Sum.inr i) b := by
          rw [UV.compress_of_disjoint_of_le]
          · rw [Finset.sdiff_empty, Finset.sup_eq_union, Finset.union_comm, Finset.insert_eq]
          · simp [Finset.disjoint_singleton_left, hi]
          · exact bot_le
        rw [hc] at hbs; rw [← hbs] at hns; exact absurd (h _ hb) hns
  · intro hs
    refine Or.inl ⟨hs, ?_⟩
    by_cases hi : Sum.inr i ∈ s
    · have : UV.compress ({Sum.inr i} : Finset (α ⊕ α)) ∅ s = s := by
        rw [UV.compress]; simp [Finset.disjoint_singleton_left, hi]
      rw [this]; exact hs
    · have hc : UV.compress ({Sum.inr i} : Finset (α ⊕ α)) ∅ s = insert (Sum.inr i) s := by
        rw [UV.compress_of_disjoint_of_le]
        · rw [Finset.sdiff_empty, Finset.sup_eq_union, Finset.union_comm, Finset.insert_eq]
        · simp [Finset.disjoint_singleton_left, hi]
        · exact bot_le
      rw [hc]; exact h _ hs


theorem doubleCompress_eq_self (i : α) {𝒜 : Finset (Finset (α ⊕ α))}
    (hd : IsDownAtLeft i 𝒜) (hu : IsUpAtRight i 𝒜) :
    doubleCompress i 𝒜 = 𝒜 := by
  unfold doubleCompress
  rw [downLeft_eq_self i hd, upRight_eq_self i hu]


theorem boxDoubled_card_le_mul_of_fixed (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card :=
  card_boxDoubled_le_mul 𝒜 ℬ


end StatMech
