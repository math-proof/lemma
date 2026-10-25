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
import Def.StatisticalMechanics.Code.Walls.rc22doublecover.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


@[simp] theorem rc22_mem_complFam (ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc22_complFam ℬ ↔ Sᶜ ∈ ℬ := by
  rw [rc22_complFam, Finset.mem_image]
  constructor
  · rintro ⟨T, hT, rfl⟩; rwa [compl_compl]
  · intro h; exact ⟨Sᶜ, h, compl_compl S⟩

theorem rc22_card_complFam (ℬ : Finset (Finset α)) : #(rc22_complFam ℬ) = #ℬ := by
  rw [rc22_complFam]
  exact Finset.card_image_of_injective _ (compl_injective)

open Classical in


theorem rc22_reflInter_eq_inter_complFam (𝒜 ℬ : Finset (Finset α)) :
    rc10_reflInter 𝒜 ℬ = 𝒜 ∩ rc22_complFam ℬ := by
  ext S
  rw [rc20_mem_reflInter, Finset.mem_inter, rc22_mem_complFam]


open Classical in


theorem rc22_famCylBox_subset_boxSupp (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ rc10_boxSupp 𝒜 ℬ := by
  intro S hS
  rw [rc21_mem_famCylBox] at hS
  obtain ⟨K, L, hKL, hKA, hLB⟩ := hS
  rw [rc10_boxSupp, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, S ∩ K, S ∩ L, ?_, Finset.inter_subset_left,
    Finset.inter_subset_left, ?_, ?_⟩
  · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hKL)
  · exact hKA (S ∩ K) (by rw [Finset.inter_assoc, Finset.inter_self])
  · exact hLB (S ∩ L) (by rw [Finset.inter_assoc, Finset.inter_self])


open Classical in


theorem rc22_famCylBox_le_reflInter_of_upperSet {n : ℕ} {𝒜 ℬ : Finset (Finset (Fin n))}
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset (Fin n)))) (hℬ : IsUpperSet (ℬ : Set (Finset (Fin n)))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  le_trans (Finset.card_le_card (rc22_famCylBox_subset_boxSupp 𝒜 ℬ))
    (rc16_bkrSetFamily n 𝒜 ℬ h𝒜 hℬ)


end StatMech.Walls
