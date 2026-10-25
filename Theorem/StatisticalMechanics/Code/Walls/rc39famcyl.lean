/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc39famcyl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc38butterflymono
import Theorem.StatisticalMechanics.Code.Walls.rc22doublecover.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc23boxmono
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc39_reflInter_right_univ (𝒜 : Finset (Finset α)) :
    rc10_reflInter 𝒜 univ = 𝒜 := by
  ext S; rw [rc20_mem_reflInter]; simp [Finset.mem_univ]

open Classical in


theorem rc39_famCylBox_right_univ_subset (𝒜 : Finset (Finset α)) :
    rc20_famCylBox 𝒜 univ ⊆ 𝒜 := by
  intro S hS
  rw [rc21_mem_famCylBox] at hS
  obtain ⟨K, L, _, hKA, _⟩ := hS
  exact hKA S rfl

open Classical in


theorem rc39_famCylBox_le_reflInter_right_univ (𝒜 : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 univ) ≤ #(rc10_reflInter 𝒜 univ) := by
  rw [rc39_reflInter_right_univ]
  exact Finset.card_le_card (rc39_famCylBox_right_univ_subset 𝒜)

open Classical in


theorem rc39_famCylBox_left_univ_subset (ℬ : Finset (Finset α)) :
    rc20_famCylBox univ ℬ ⊆ ℬ := by
  intro S hS
  rw [rc21_mem_famCylBox] at hS
  obtain ⟨K, L, _, _, hLB⟩ := hS
  exact hLB S rfl

open Classical in


theorem rc39_card_reflInter_left_univ (ℬ : Finset (Finset α)) :
    #(rc10_reflInter univ ℬ) = #ℬ := by
  rw [rc22_reflInter_eq_inter_complFam, Finset.univ_inter, rc22_card_complFam]

open Classical in


theorem rc39_famCylBox_le_reflInter_left_univ (ℬ : Finset (Finset α)) :
    #(rc20_famCylBox univ ℬ) ≤ #(rc10_reflInter univ ℬ) := by
  rw [rc39_card_reflInter_left_univ]
  exact Finset.card_le_card (rc39_famCylBox_left_univ_subset ℬ)


open Classical in


theorem rc39_famCylBox_le_reflInter_of_monotone {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin n))}
    (h : (IsUpperSet (𝒜 : Set (Finset (Fin n))) ∧ IsUpperSet (ℬ : Set (Finset (Fin n))))
        ∨ (IsLowerSet (𝒜 : Set (Finset (Fin n))) ∧ IsLowerSet (ℬ : Set (Finset (Fin n))))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rcases h with ⟨h𝒜, hℬ⟩ | ⟨h𝒜, hℬ⟩
  · exact rc22_famCylBox_le_reflInter_of_upperSet h𝒜 hℬ
  · exact rc23_boxDownsetBase_proof h𝒜 hℬ


end StatMech.Walls
