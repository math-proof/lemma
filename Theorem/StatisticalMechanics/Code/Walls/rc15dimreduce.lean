/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc15dimreduce.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc14reimerinduct
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc15_reflE_mem_erase (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α) (S : Finset α)
    (haE : a ∈ E) (haS : a ∈ S) :
    S.erase a ∈ rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)
      ↔ S ∈ rc14_reflE E 𝒜 ℬ := by
  rw [rc14_mem_reflE, rc14_mem_reflE, mem_memberSubfamily, mem_nonMemberSubfamily]
  constructor
  · rintro ⟨hsub, ⟨hmem, _⟩, hcompl, hcomplna⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases eq_or_ne x a with rfl | hxa
      · exact haE
      · exact (Finset.mem_erase.mp (hsub (Finset.mem_erase.mpr ⟨hxa, hx⟩))).2
    · rwa [insert_erase haS] at hmem
    · have : E \ S = (E.erase a) \ (S.erase a) := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro ⟨hxE, hxS⟩
          exact ⟨⟨fun h => hxS (h ▸ haS), hxE⟩, fun h => hxS h.2⟩
        · rintro ⟨⟨hxa, hxE⟩, h⟩
          exact ⟨hxE, fun hxS => h ⟨hxa, hxS⟩⟩
      rwa [this]
  · rintro ⟨hsub, hmem, hcompl⟩
    refine ⟨?_, ⟨?_, by simp [Finset.mem_erase]⟩, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_erase] at hx ⊢
      exact ⟨hx.1, hsub hx.2⟩
    · rwa [insert_erase haS]
    · have : (E.erase a) \ (S.erase a) = E \ S := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro ⟨⟨hxa, hxE⟩, h⟩
          exact ⟨hxE, fun hxS => h ⟨hxa, hxS⟩⟩
        · rintro ⟨hxE, hxS⟩
          exact ⟨⟨fun h => hxS (h ▸ haS), hxE⟩, fun h => hxS h.2⟩
      rwa [this]
    · simp only [Finset.mem_sdiff, Finset.mem_erase]
      rintro ⟨⟨hcon, _⟩, _⟩; exact hcon rfl

open Classical in


theorem rc15_reflE_mem_id (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α) (S : Finset α)
    (haE : a ∈ E) (haS : a ∉ S) :
    S ∈ rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a)
      ↔ S ∈ rc14_reflE E 𝒜 ℬ := by
  rw [rc14_mem_reflE, rc14_mem_reflE, mem_nonMemberSubfamily, mem_memberSubfamily]
  have hcompl : insert a ((E.erase a) \ S) = E \ S := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨⟨_, hxE⟩, hxS⟩)
      · exact ⟨haE, haS⟩
      · exact ⟨hxE, hxS⟩
    · rintro ⟨hxE, hxS⟩
      rcases eq_or_ne x a with rfl | hxa
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hxa, hxE⟩, hxS⟩
  have haEsub : a ∉ (E.erase a) \ S := by simp [Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro ⟨hsub, ⟨hmem, _⟩, hcomplmem, _⟩
    refine ⟨?_, hmem, ?_⟩
    · exact hsub.trans (Finset.erase_subset a E)
    · rwa [hcompl] at hcomplmem
  · rintro ⟨hsub, hmem, hcomplmem⟩
    refine ⟨?_, ⟨hmem, haS⟩, ?_, haEsub⟩
    · intro x hx
      rw [Finset.mem_erase]
      exact ⟨fun h => haS (h ▸ hx), hsub hx⟩
    · rw [hcompl]; exact hcomplmem

open Classical in


theorem rc15_card_reflE_slice (E : Finset α) (𝒜 ℬ : Finset (Finset α)) (a : α) (haE : a ∈ E) :
    #(rc14_reflE E 𝒜 ℬ)
      = #(rc14_reflE (E.erase a) (𝒜.nonMemberSubfamily a) (ℬ.memberSubfamily a))
        + #(rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a)) := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := rc14_reflE E 𝒜 ℬ) (p := fun S => a ∈ S),
    add_comm]
  congr 1
  · 
    apply Finset.card_bij (fun S _ => S)
    · intro S hS
      simp only [Finset.mem_filter] at hS ⊢
      exact (rc15_reflE_mem_id E 𝒜 ℬ a S haE hS.2).mpr hS.1
    · intro S _ S' _ h; exact h
    · intro S hS
      rw [rc14_mem_reflE] at hS
      have haS : a ∉ S := by
        intro h
        have := (Finset.mem_erase.mp (hS.1 h)).1; exact this rfl
      refine ⟨S, ?_, rfl⟩
      simp only [Finset.mem_filter]
      exact ⟨(rc15_reflE_mem_id E 𝒜 ℬ a S haE haS).mp (rc14_mem_reflE _ _ _ _ |>.mpr hS), haS⟩
  · 
    apply Finset.card_bij (fun S _ => S.erase a)
    · intro S hS
      simp only [Finset.mem_filter] at hS
      exact (rc15_reflE_mem_erase E 𝒜 ℬ a S haE hS.2).mpr hS.1
    · intro S hS S' hS' h
      simp only [Finset.mem_filter] at hS hS'
      have := congrArg (insert a) h
      rwa [insert_erase hS.2, insert_erase hS'.2] at this
    · intro R hR
      have hRmem : R ∈ rc14_reflE (E.erase a) (𝒜.memberSubfamily a) (ℬ.nonMemberSubfamily a) := hR
      rw [rc14_mem_reflE, mem_memberSubfamily] at hRmem
      obtain ⟨hRsub, ⟨hins, haR⟩, _⟩ := hRmem
      refine ⟨insert a R, ?_, ?_⟩
      · simp only [Finset.mem_filter]
        refine ⟨?_, Finset.mem_insert_self a R⟩
        rw [← rc15_reflE_mem_erase E 𝒜 ℬ a (insert a R) haE (Finset.mem_insert_self a R),
          Finset.erase_insert haR]
        exact hR
      · rw [Finset.erase_insert haR]


end StatMech.Walls
