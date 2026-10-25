/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc49doubled.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc48cover.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc49doubled.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc49_wall_of_hall (𝒜 ℬ : Finset (Finset α)) (h : rc49_HallCond 𝒜 ℬ) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  set box := rc20_famCylBox 𝒜 ℬ with hbox
  
  let t : {S : Finset α // S ∈ box} → Finset (Finset α) :=
    fun S => rc49_neighbourhood 𝒜 ℬ S.1
  have hHall : ∀ s : Finset {S : Finset α // S ∈ box}, #s ≤ #(s.biUnion t) := by
    intro s
    
    have hsub : s.image (Subtype.val) ⊆ box := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨y, _, rfl⟩ := hx
      exact y.2
    have hcard_s : #s = #(s.image (Subtype.val)) := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
    have hbiU : (s.image (Subtype.val)).biUnion (rc49_neighbourhood 𝒜 ℬ) = s.biUnion t := by
      ext R
      simp only [Finset.mem_biUnion, Finset.mem_image, t]
      constructor
      · rintro ⟨x, ⟨y, hy, rfl⟩, hR⟩; exact ⟨y, hy, hR⟩
      · rintro ⟨y, hy, hR⟩; exact ⟨y.1, ⟨y, hy, rfl⟩, hR⟩
    rw [hcard_s, ← hbiU]
    exact h _ hsub
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  
  calc #box = #(univ : Finset {S : Finset α // S ∈ box}) := by
              rw [Finset.card_univ, Fintype.card_coe]
    _ ≤ #(rc10_reflInter 𝒜 ℬ) := by
              refine Finset.card_le_card_of_injOn f (fun S _ => ?_) (fun a _ b _ hab => hfinj hab)
              exact rc49_neighbourhood_subset_reflInter 𝒜 ℬ S.1 (hfmem S)

end StatMech.Walls
