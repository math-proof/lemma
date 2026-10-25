/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc45doubledcover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc44boxineq.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] in


theorem rc45_slab1_card (a : α) (𝒜 : Finset (Finset α)) :
    (rc44_slab1 a 𝒜).card = (𝒜.filter (fun S => a ∈ S)).card := by
  rw [rc44_slab1]
  refine Finset.card_image_of_injOn ?_
  intro S hS S' hS' h
  simp only at h
  rw [Finset.mem_coe, Finset.mem_filter] at hS hS'
  rw [← Finset.insert_erase hS.2, ← Finset.insert_erase hS'.2, h]

omit [Fintype α] in


theorem rc45_slab_card_partition (a : α) (𝒜 : Finset (Finset α)) :
    𝒜.card = (rc44_slab0 a 𝒜).card + (rc44_slab1 a 𝒜).card := by
  rw [rc45_slab1_card, rc44_slab0]
  rw [add_comm]
  exact (Finset.card_filter_add_card_filter_not (fun S => a ∈ S)).symm


open Classical in


theorem rc45_famCylBoxE_card_diagonal_ub (E : Finset α) (a : α) (𝒜 ℬ : Finset (Finset α)) :
    (rc44_famCylBoxE E 𝒜 ℬ).card
      ≤ (rc44_famCylBoxE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab0 a ℬ)).card
        + (rc44_famCylBoxE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab1 a ℬ)).card := by
  rw [rc45_slab_card_partition a (rc44_famCylBoxE E 𝒜 ℬ)]
  exact Nat.add_le_add
    (Finset.card_le_card (rc44_slab0_famCylBoxE_subset E a 𝒜 ℬ))
    (Finset.card_le_card (rc44_slab1_famCylBoxE_subset E a 𝒜 ℬ))


open Classical in


theorem rc45_reflInterE_card_antidiagonal (E : Finset α) (a : α) (haE : a ∈ E)
    (𝒜 ℬ : Finset (Finset α)) :
    (rc44_reflInterE E 𝒜 ℬ).card
      = (rc44_reflInterE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab1 a ℬ)).card
        + (rc44_reflInterE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab0 a ℬ)).card :=
  rc44_reflInterE_card_recursion E a haE 𝒜 ℬ


end StatMech.Walls
