/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc33nonlocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc32reflwitness.Part2
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc33nonlocal
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc33_admOneSidedA_subset_reflInter (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) : rc33_admOneSidedA n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
  intro R hR
  rw [rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq] at hR
  obtain ⟨_, hRA, hRB, _⟩ := hR
  rw [rc20_mem_reflInter]; exact ⟨hRA, hRB⟩


theorem rc33_admOneSidedB_subset_reflInter (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) : rc33_admOneSidedB n 𝒜 ℬ S ⊆ rc10_reflInter 𝒜 ℬ := by
  intro R hR
  rw [rc33_admOneSidedB, Finset.mem_filter, decide_eq_true_eq] at hR
  obtain ⟨_, hRA, hRB, _⟩ := hR
  rw [rc20_mem_reflInter]; exact ⟨hRA, hRB⟩


theorem rc33_admComp_subset_bothSided (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) : rc21_admComp n 𝒜 ℬ S ⊆ rc33_admBothSided n 𝒜 ℬ S := by
  intro R hR
  rw [rc21_admComp, Finset.mem_filter, decide_eq_true_eq] at hR
  obtain ⟨_, K, _, L, _, hKL, hKA, hLB, hRK, hRL⟩ := hR
  rw [rc33_admBothSided, Finset.mem_filter, decide_eq_true_eq]
  have hmem : R ∈ rc10_reflInter 𝒜 ℬ :=
    rc21_localRefl_mem_reflInter ((rc20_traceClass_subset_iff n K S 𝒜).mp hKA)
      ((rc20_traceClass_subset_iff n L S ℬ).mp hLB) hRK hRL
  rw [rc20_mem_reflInter] at hmem
  exact ⟨Finset.mem_univ _, hmem.1, hmem.2,
    ⟨K, Finset.mem_univ _, hKA, hRK⟩, ⟨L, Finset.mem_univ _, hLB, hRL⟩⟩


open Classical in


theorem rc33_wall_of_hallOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (hHall : ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  set box := rc20_famCylBox 𝒜 ℬ with hbox
  set t : (↥box) → Finset (Finset (Fin n)) := fun x => rc33_admOneSidedA n 𝒜 ℬ x.val with ht
  
  have hHall' : ∀ s : Finset (↥box), #s ≤ #(s.biUnion t) := by
    intro s
    have hsub : s.image (Subtype.val) ⊆ box := by
      intro x hx; rw [Finset.mem_image] at hx; obtain ⟨y, _, rfl⟩ := hx; exact y.property
    have h𝒯 := hHall (s.image Subtype.val) (Finset.mem_powerset.mpr hsub)
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at h𝒯
    rwa [Finset.image_biUnion] at h𝒯
  
  obtain ⟨g, hinj, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall'
  have hg_ri : ∀ x, g x ∈ rc10_reflInter 𝒜 ℬ := fun x =>
    rc33_admOneSidedA_subset_reflInter n 𝒜 ℬ x.val (hmem x)
  
  have hcard : Fintype.card (↥box) ≤ Fintype.card (↥(rc10_reflInter 𝒜 ℬ)) := by
    refine Fintype.card_le_of_injective (fun x => (⟨g x, hg_ri x⟩ : ↥(rc10_reflInter 𝒜 ℬ))) ?_
    intro a b hab
    exact hinj (Subtype.ext_iff.mp hab)
  rwa [Fintype.card_coe, Fintype.card_coe] at hcard


open Classical in


theorem rc33_hallComplete_iff_wall (𝒜 ℬ : Finset (Finset α)) :
    (∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
        𝒯.card ≤ (𝒯.biUnion (fun _ => rc10_reflInter 𝒜 ℬ)).card) ↔
      #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  constructor
  · intro h
    have hbox := h (rc20_famCylBox 𝒜 ℬ) (Finset.mem_powerset.mpr (Finset.Subset.refl _))
    rcases (rc20_famCylBox 𝒜 ℬ).eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; simp
    · rwa [show (rc20_famCylBox 𝒜 ℬ).biUnion (fun _ => rc10_reflInter 𝒜 ℬ)
          = rc10_reflInter 𝒜 ℬ from ?_] at hbox
      apply Finset.Subset.antisymm
      · exact Finset.biUnion_subset.mpr (fun _ _ => Finset.Subset.refl _)
      · obtain ⟨i, hi⟩ := hne
        exact fun x hx => Finset.mem_biUnion.mpr ⟨i, hi, hx⟩
  · intro hcard 𝒯 h𝒯
    rw [Finset.mem_powerset] at h𝒯
    rcases 𝒯.eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; simp
    · rw [show 𝒯.biUnion (fun _ => rc10_reflInter 𝒜 ℬ) = rc10_reflInter 𝒜 ℬ from ?_]
      · exact le_trans (Finset.card_le_card h𝒯) hcard
      · apply Finset.Subset.antisymm
        · exact Finset.biUnion_subset.mpr (fun _ _ => Finset.Subset.refl _)
        · obtain ⟨i, hi⟩ := hne
          exact fun x hx => Finset.mem_biUnion.mpr ⟨i, hi, hx⟩


end StatMech.Walls
