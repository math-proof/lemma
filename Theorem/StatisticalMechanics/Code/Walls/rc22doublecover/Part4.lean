/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc22doublecover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc21persupport.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
import Theorem.StatisticalMechanics.Code.Walls.rc16sliceunion
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Walls.rc22doublecover.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


variable {β : Type*} [DecidableEq β]


theorem rc22_uvCompress_singleton (a : β) (s : Finset β) :
    UV.compress ({a} : Finset β) ∅ s = insert a s := by
  by_cases ha : a ∈ s
  · rw [UV.compress]
    simp only [Finset.disjoint_singleton_left, ha, not_true, false_and, if_false]
    rw [insert_eq_of_mem ha]
  · rw [UV.compress_of_disjoint_of_le]
    · rw [Finset.sdiff_empty, Finset.sup_eq_union, Finset.union_comm, Finset.insert_eq]
    · simp [Finset.disjoint_singleton_left, ha]
    · exact bot_le


theorem rc22_mem_upComp (i : β) (𝒜 : Finset (Finset β)) (s : Finset β) :
    s ∈ rc22_upComp i 𝒜 ↔
      (s ∈ 𝒜 ∧ insert i s ∈ 𝒜) ∨ (s ∉ 𝒜 ∧ ∃ b ∈ 𝒜, insert i b = s) := by
  unfold rc22_upComp; rw [UV.mem_compression]; simp_rw [rc22_uvCompress_singleton]


theorem rc22_upComp_card (i : β) (𝒜 : Finset (Finset β)) : (rc22_upComp i 𝒜).card = 𝒜.card := by
  unfold rc22_upComp; exact UV.card_compression _ _ _


theorem rc22_upComp_nonMemberSubfamily (i : β) (𝒞 : Finset (Finset β)) :
    (rc22_upComp i 𝒞).nonMemberSubfamily i = 𝒞.memberSubfamily i ∩ 𝒞.nonMemberSubfamily i := by
  ext s
  simp only [mem_nonMemberSubfamily, mem_inter, mem_memberSubfamily, rc22_mem_upComp]
  constructor
  · rintro ⟨h, hns⟩
    rcases h with ⟨hsC, hins⟩ | ⟨_, b, _, hb⟩
    · exact ⟨⟨hins, hns⟩, hsC, hns⟩
    · exact absurd (by rw [← hb]; exact mem_insert_self i b) hns
  · rintro ⟨⟨hins, _⟩, hsC, hns⟩; exact ⟨Or.inl ⟨hsC, hins⟩, hns⟩


theorem rc22_upComp_memberSubfamily (i : β) (𝒞 : Finset (Finset β)) :
    (rc22_upComp i 𝒞).memberSubfamily i = 𝒞.memberSubfamily i ∪ 𝒞.nonMemberSubfamily i := by
  ext s
  simp only [mem_memberSubfamily, mem_union, mem_nonMemberSubfamily, rc22_mem_upComp]
  constructor
  · rintro ⟨h, hns⟩
    rcases h with ⟨hsC, _⟩ | ⟨_, b, hbC, hb⟩
    · exact Or.inl ⟨hsC, hns⟩
    · by_cases hib : i ∈ b
      · rw [insert_eq_of_mem hib] at hb; exact Or.inl ⟨hb ▸ hbC, hns⟩
      · have hbs : b = s := by
          have := congrArg (fun t => Finset.erase t i) hb
          simp only [Finset.erase_insert hib, Finset.erase_insert hns] at this; exact this
        exact Or.inr ⟨hbs ▸ hbC, hns⟩
  · intro h
    rcases h with ⟨hins, hns⟩ | ⟨hsC, hns⟩
    · exact ⟨Or.inl ⟨hins, by rw [insert_idem]; exact hins⟩, hns⟩
    · refine ⟨?_, hns⟩
      by_cases hins : insert i s ∈ 𝒞
      · exact Or.inl ⟨hins, by rw [insert_idem]; exact hins⟩
      · exact Or.inr ⟨hins, s, hsC, rfl⟩


theorem rc22_downInterUp_le (i : β) (𝒜 𝒞 : Finset (Finset β)) :
    #(Down.compression i 𝒜 ∩ rc22_upComp i 𝒞) ≤ #(𝒜 ∩ 𝒞) := by
  rw [← card_memberSubfamily_add_card_nonMemberSubfamily i (Down.compression i 𝒜 ∩ rc22_upComp i 𝒞),
      ← card_memberSubfamily_add_card_nonMemberSubfamily i (𝒜 ∩ 𝒞),
      memberSubfamily_inter, nonMemberSubfamily_inter, memberSubfamily_inter,
      nonMemberSubfamily_inter, rc2_downComp_memberSubfamily, rc2_downComp_nonMemberSubfamily,
      rc22_upComp_memberSubfamily, rc22_upComp_nonMemberSubfamily]
  exact rc22_fiber_inter_ineq _ _ _ _


theorem rc22_mem_complImage [Fintype β] (ℬ : Finset (Finset β)) (s : Finset β) :
    s ∈ ℬ.image compl ↔ sᶜ ∈ ℬ := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨T, hT, rfl⟩; rwa [compl_compl]
  · intro h; exact ⟨sᶜ, h, compl_compl s⟩


theorem rc22_complImage_downCompression [Fintype β] (i : β) (ℬ : Finset (Finset β)) :
    (Down.compression i ℬ).image compl = rc22_upComp i (ℬ.image compl) := by
  ext s
  rw [rc22_mem_complImage, rc22_mem_upComp, Down.mem_compression]
  simp only [rc22_mem_complImage]
  rw [Finset.compl_insert]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, h2⟩
    · have his : i ∈ s := by
        by_contra hc
        exact h1 (by rwa [insert_eq_of_mem (Finset.mem_compl.mpr hc)] at h2)
      refine Or.inr ⟨h1, s.erase i, ?_, Finset.insert_erase his⟩
      rw [compl_erase]; exact h2
  · rintro (⟨h1, h2⟩ | ⟨h1, b, hb1, hb2⟩)
    · exact Or.inl ⟨h1, h2⟩
    · refine Or.inr ⟨h1, ?_⟩
      have hib : i ∉ b := by
        intro hc; rw [insert_eq_of_mem hc] at hb2; exact h1 (hb2 ▸ hb1)
      subst hb2
      rw [Finset.compl_insert, Finset.insert_erase (Finset.mem_compl.mpr hib)]
      exact hb1


theorem rc22_reflInter_downDown_antitone [Fintype β] (i : β) (𝒜 ℬ : Finset (Finset β)) :
    #(rc10_reflInter (Down.compression i 𝒜) (Down.compression i ℬ))
      ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rw [rc22_reflInter_eq_inter_complFam, rc22_reflInter_eq_inter_complFam, rc22_complFam,
    rc22_complFam, rc22_complImage_downCompression]
  exact rc22_downInterUp_le i 𝒜 (ℬ.image compl)


theorem rc22_reflInter_iterDownComp_antitone [Fintype β] (cs : List β) (𝒜 ℬ : Finset (Finset β)) :
    #(rc10_reflInter (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  induction cs with
  | nil => rw [iterDownComp_nil, iterDownComp_nil]
  | cons i cs ih =>
    rw [iterDownComp_cons, iterDownComp_cons]
    exact le_trans (rc22_reflInter_downDown_antitone i _ _) ih


end StatMech.Walls
