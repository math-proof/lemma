/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve2.Part2
import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Def.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3.Part2
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


theorem downComp_eq_image_cmap (i : α) (𝒜 : Finset (Finset α)) :
    Down.compression i 𝒜 = 𝒜.image (cmap i 𝒜) := by
  ext s
  rw [Down.mem_compression, mem_image]
  constructor
  · rintro (⟨hs, herase⟩ | ⟨hns, hins⟩)
    · refine ⟨s, hs, ?_⟩
      unfold cmap; rw [if_neg]; rintro ⟨_, hc⟩; exact hc herase
    · have hi : i ∉ s := fun hi => hns (by rwa [insert_eq_of_mem hi] at hins)
      refine ⟨insert i s, hins, ?_⟩
      unfold cmap
      rw [if_pos ⟨mem_insert_self _ _, by rw [erase_insert hi]; exact hns⟩, erase_insert hi]
  · rintro ⟨t, ht, rfl⟩
    unfold cmap
    by_cases hcond : i ∈ t ∧ t.erase i ∉ 𝒜
    · rw [if_pos hcond]
      exact Or.inr ⟨hcond.2, by rw [insert_erase hcond.1]; exact ht⟩
    · rw [if_neg hcond]
      refine Or.inl ⟨ht, ?_⟩
      by_cases hi : i ∈ t
      · by_contra hc; exact hcond ⟨hi, hc⟩
      · rw [erase_eq_of_notMem hi]; exact ht


theorem cmap_injOn (i : α) (𝒜 : Finset (Finset α)) :
    Set.InjOn (cmap i 𝒜) (𝒜 : Set (Finset α)) := by
  intro s hs t ht heq
  rw [Finset.mem_coe] at hs ht
  unfold cmap at heq
  by_cases hcs : i ∈ s ∧ s.erase i ∉ 𝒜 <;> by_cases hct : i ∈ t ∧ t.erase i ∉ 𝒜
  · rw [if_pos hcs, if_pos hct] at heq
    rw [← insert_erase hcs.1, ← insert_erase hct.1, heq]
  · rw [if_pos hcs, if_neg hct] at heq; exact absurd (heq ▸ ht) hcs.2
  · rw [if_neg hcs, if_pos hct] at heq; exact absurd (heq ▸ hs) hct.2
  · rw [if_neg hcs, if_neg hct] at heq; exact heq


theorem cmap_card_le (i : α) (𝒜 : Finset (Finset α)) (s : Finset α) :
    (cmap i 𝒜 s).card ≤ s.card := by
  unfold cmap; split
  · exact card_erase_le
  · exact le_refl _


end StatMech
