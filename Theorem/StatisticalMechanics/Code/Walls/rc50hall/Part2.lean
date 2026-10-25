/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc49doubled.Part4
import Def.StatisticalMechanics.Code.Walls.rc50hall
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc50_wall_of_injectiveSelection {𝒜 ℬ : Finset (Finset α)}
    (h : rc50_InjectiveSelection 𝒜 ℬ) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  obtain ⟨w, hwit, hinj⟩ := h
  refine Finset.card_le_card_of_injOn (fun S => rc49_jointImage S (w S).1 (w S).2) ?_ hinj
  intro S hS
  rw [Finset.mem_coe] at hS
  obtain ⟨hKL, hKA, hLB⟩ := hwit S hS
  exact rc49_jointImage_mem_reflInter hKL hKA hLB

open Classical in


theorem rc50_hall_of_injectiveSelection {𝒜 ℬ : Finset (Finset α)}
    (h : rc50_InjectiveSelection 𝒜 ℬ) : rc49_HallCond 𝒜 ℬ := by
  obtain ⟨w, hwit, hinj⟩ := h
  intro W hW
  refine Finset.card_le_card_of_injOn (fun S => rc49_jointImage S (w S).1 (w S).2) ?_ ?_
  · intro S hSW
    rw [Finset.mem_coe] at hSW
    have hSbox : S ∈ rc20_famCylBox 𝒜 ℬ := hW hSW
    obtain ⟨hKL, hKA, hLB⟩ := hwit S hSbox
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨S, hSW, rc50_jointImage_mem_neighbourhood hKL hKA hLB⟩
  · intro S hSW S' hSW' heq
    rw [Finset.mem_coe] at hSW hSW'
    exact hinj (hW hSW) (hW hSW') heq

open Classical in


theorem rc50_injectiveSelection_of_hall {𝒜 ℬ : Finset (Finset α)}
    (h : rc49_HallCond 𝒜 ℬ) : rc50_InjectiveSelection 𝒜 ℬ := by
  let box := rc20_famCylBox 𝒜 ℬ
  
  let t : {S : Finset α // S ∈ box} → Finset (Finset α) :=
    fun S => rc49_neighbourhood 𝒜 ℬ S.1
  have hHall : ∀ s : Finset {S : Finset α // S ∈ box}, #s ≤ #(s.biUnion t) := by
    intro s
    have hsub : s.image (Subtype.val) ⊆ box := by
      intro x hx; rw [Finset.mem_image] at hx; obtain ⟨y, _, rfl⟩ := hx; exact y.2
    have hcard_s : #s = #(s.image (Subtype.val)) := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
    have hbiU : (s.image (Subtype.val)).biUnion (rc49_neighbourhood 𝒜 ℬ) = s.biUnion t := by
      ext R; simp only [Finset.mem_biUnion, Finset.mem_image, t]
      constructor
      · rintro ⟨x, ⟨y, hy, rfl⟩, hR⟩; exact ⟨y, hy, hR⟩
      · rintro ⟨y, hy, hR⟩; exact ⟨y.1, ⟨y, hy, rfl⟩, hR⟩
    rw [hcard_s, ← hbiU]; exact h _ hsub
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  
  have hchoose : ∀ S : {S : Finset α // S ∈ box}, ∃ p : Finset α × Finset α,
      Disjoint p.1 p.2 ∧
      (∀ T : Finset α, T ∩ p.1 = S.1 ∩ p.1 → T ∈ 𝒜) ∧
      (∀ T : Finset α, T ∩ p.2 = S.1 ∩ p.2 → T ∈ ℬ) ∧
      rc49_jointImage S.1 p.1 p.2 = f S := by
    intro S
    have hmem := hfmem S
    simp only [t, rc49_neighbourhood, Finset.mem_filter] at hmem
    obtain ⟨_, K, L, hKL, hKA, hLB, hEq⟩ := hmem
    exact ⟨(K, L), hKL, hKA, hLB, hEq⟩
  choose g hg using hchoose
  
  set w : Finset α → Finset α × Finset α := fun S => if hS : S ∈ box then g ⟨S, hS⟩ else (∅, ∅)
    with hw
  have hwbox : ∀ (S : Finset α) (hS : S ∈ box), w S = g ⟨S, hS⟩ := by
    intro S hS; rw [hw]; simp only [dif_pos hS]
  refine ⟨w, ?_, ?_⟩
  · intro S hS
    have hSbox : S ∈ box := hS
    rw [hwbox S hSbox]
    obtain ⟨hKL, hKA, hLB, _⟩ := hg ⟨S, hSbox⟩
    exact ⟨hKL, hKA, hLB⟩
  · intro S hS S' hS' heq
    have hSbox : S ∈ box := hS
    have hSbox' : S' ∈ box := hS'
    simp only [hwbox S hSbox, hwbox S' hSbox'] at heq
    have e1 := (hg ⟨S, hSbox⟩).2.2.2
    have e2 := (hg ⟨S', hSbox'⟩).2.2.2
    rw [e1, e2] at heq
    exact congrArg Subtype.val (hfinj heq)

open Classical in


theorem rc50_hall_iff_injectiveSelection (𝒜 ℬ : Finset (Finset α)) :
    rc49_HallCond 𝒜 ℬ ↔ rc50_InjectiveSelection 𝒜 ℬ :=
  ⟨rc50_injectiveSelection_of_hall, rc50_hall_of_injectiveSelection⟩


end StatMech.Walls
