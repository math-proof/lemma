/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc47reimer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc46butterfly.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc47_famCylBox_subset_inter (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 ∩ ℬ := by
  intro S hS
  rw [rc20_famCylBox, Finset.mem_filter] at hS
  obtain ⟨_, K, L, _, hKA, hLB⟩ := hS
  rw [Finset.mem_inter]
  exact ⟨hKA S rfl, hLB S rfl⟩

open Classical in

theorem rc47_famCylBox_subset_left (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ 𝒜 :=
  (rc47_famCylBox_subset_inter 𝒜 ℬ).trans (Finset.inter_subset_left)

open Classical in

theorem rc47_famCylBox_subset_right (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ ℬ :=
  (rc47_famCylBox_subset_inter 𝒜 ℬ).trans (Finset.inter_subset_right)

open Classical in


theorem rc47_reflInter_subset_left (𝒜 ℬ : Finset (Finset α)) :
    rc10_reflInter 𝒜 ℬ ⊆ 𝒜 := by
  intro R hR
  rw [rc20_mem_reflInter] at hR
  exact hR.1

open Classical in


theorem rc47_reflInter_card_le_right (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) ≤ #ℬ := by
  refine Finset.card_le_card_of_injOn (fun R => Rᶜ) ?_ ?_
  · intro R hR
    rw [Finset.mem_coe, rc20_mem_reflInter] at hR
    exact hR.2
  · intro R _ R' _ h
    have := congrArg (compl : Finset α → Finset α) h
    rwa [compl_compl, compl_compl] at this

open Classical in


theorem rc47_reflInter_card_le_min (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) ≤ min (#𝒜) (#ℬ) :=
  le_min (Finset.card_le_card (rc47_reflInter_subset_left 𝒜 ℬ))
    (rc47_reflInter_card_le_right 𝒜 ℬ)

open Classical in


theorem rc47_famCylBox_card_le_min (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ min (#𝒜) (#ℬ) :=
  le_min (Finset.card_le_card (rc47_famCylBox_subset_left 𝒜 ℬ))
    (Finset.card_le_card (rc47_famCylBox_subset_right 𝒜 ℬ))


open Classical in


theorem rc47_famCylBox_le_reflInter_of_interCard (𝒜 ℬ : Finset (Finset α))
    (h : #(𝒜 ∩ ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  (Finset.card_le_card (rc47_famCylBox_subset_inter 𝒜 ℬ)).trans h

open Classical in


theorem rc47_famCylBox_le_reflInter_of_subset (𝒜 ℬ : Finset (Finset α))
    (h : rc20_famCylBox 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  Finset.card_le_card h


end StatMech.Walls
