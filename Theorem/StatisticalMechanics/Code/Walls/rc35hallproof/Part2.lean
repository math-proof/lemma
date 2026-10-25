/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc35hallproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc34butterfly.Part2
import Def.StatisticalMechanics.Code.Walls.rc35hallproof.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc35_admOneSidedA_eq_biUnion_slice (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) :
    rc33_admOneSidedA n 𝒜 ℬ S
      = (rc35_awitsA n 𝒜 S).biUnion (fun K => rc35_traceSlice 𝒜 ℬ K S) := by
  apply Finset.Subset.antisymm
  · intro R hR
    rw [rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq] at hR
    obtain ⟨_, hRA, hRB, K, _, hKA, hRK⟩ := hR
    rw [Finset.mem_biUnion]
    refine ⟨K, ?_, ?_⟩
    · rw [rc35_awitsA, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hKA⟩
    · rw [rc35_traceSlice, Finset.mem_filter]
      exact ⟨(rc20_mem_reflInter 𝒜 ℬ R).mpr ⟨hRA, hRB⟩, hRK⟩
  · intro R hR
    rw [Finset.mem_biUnion] at hR
    obtain ⟨K, hK, hRslice⟩ := hR
    rw [rc35_awitsA, Finset.mem_filter] at hK
    exact rc35_slice_subset_admOneSidedA n 𝒜 ℬ
      ((rc20_traceClass_subset_iff n K S 𝒜).mp hK.2) hRslice


open Classical in


theorem rc35_hallOneSidedA_iff_injection (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
        𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card) ↔
      ∃ f : Finset (Fin n) → Finset (Fin n),
        Set.InjOn f (rc20_famCylBox 𝒜 ℬ : Set (Finset (Fin n))) ∧
        ∀ S ∈ rc20_famCylBox 𝒜 ℬ, f S ∈ rc33_admOneSidedA n 𝒜 ℬ S := by
  set box := rc20_famCylBox 𝒜 ℬ with hbox
  constructor
  · 
    intro hHall
    set t : (↥box) → Finset (Finset (Fin n)) := fun x => rc33_admOneSidedA n 𝒜 ℬ x.val with ht
    have hHall' : ∀ s : Finset (↥box), #s ≤ #(s.biUnion t) := by
      intro s
      have hsub : s.image (Subtype.val) ⊆ box := by
        intro x hx; rw [Finset.mem_image] at hx; obtain ⟨y, _, rfl⟩ := hx; exact y.property
      have h𝒯 := hHall (s.image Subtype.val) (Finset.mem_powerset.mpr hsub)
      rw [Finset.card_image_of_injective _ Subtype.val_injective] at h𝒯
      rwa [Finset.image_biUnion] at h𝒯
    obtain ⟨g, hinj, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall'
    
    refine ⟨fun S => if hS : S ∈ box then g ⟨S, hS⟩ else S, ?_, ?_⟩
    · intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      simp only [dif_pos ha, dif_pos hb] at hab
      exact congrArg Subtype.val (hinj hab)
    · intro S hS
      simp only [dif_pos hS]
      exact hmem ⟨S, hS⟩
  · 
    rintro ⟨f, hinj, hmem⟩ 𝒯 h𝒯
    rw [Finset.mem_powerset] at h𝒯
    have hInjOn𝒯 : Set.InjOn f (𝒯 : Set (Finset (Fin n))) :=
      hinj.mono (by rw [Finset.coe_subset]; exact h𝒯)
    have hImgSub : 𝒯.image f ⊆ 𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ) := by
      intro R hR
      rw [Finset.mem_image] at hR
      obtain ⟨S, hS𝒯, rfl⟩ := hR
      exact Finset.mem_biUnion.mpr ⟨S, hS𝒯, hmem S (h𝒯 hS𝒯)⟩
    calc 𝒯.card = (𝒯.image f).card :=
          (Finset.card_image_of_injOn hInjOn𝒯).symm
      _ ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card := Finset.card_le_card hImgSub


end StatMech.Walls
