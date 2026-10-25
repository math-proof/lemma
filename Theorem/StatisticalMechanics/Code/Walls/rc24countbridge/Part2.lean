/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc24countbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc23boxmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Def.StatisticalMechanics.Code.Walls.rc24countbridge
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in

theorem rc24_mem_complCylBox (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc24_complCylBox 𝒜 ℬ ↔ ∃ K : Finset α,
      (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset α, T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) := by
  rw [rc24_complCylBox, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩


open Classical in


theorem rc24_complCylBox_subset_famCylBox (𝒜 ℬ : Finset (Finset α)) :
    rc24_complCylBox 𝒜 ℬ ⊆ rc20_famCylBox 𝒜 ℬ := by
  intro S hS
  rw [rc24_mem_complCylBox] at hS
  obtain ⟨K, hKA, hKcB⟩ := hS
  rw [rc21_mem_famCylBox]
  exact ⟨K, Kᶜ, disjoint_compl_right, hKA, hKcB⟩

open Classical in


theorem rc24_famCylBox_subset_complCylBox (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ ⊆ rc24_complCylBox 𝒜 ℬ := by
  intro S hS
  rw [rc21_mem_famCylBox] at hS
  obtain ⟨K, L, hKL, hKA, hLB⟩ := hS
  rw [rc24_mem_complCylBox]
  refine ⟨K, hKA, ?_⟩
  have hLKc : L ⊆ Kᶜ := Finset.subset_compl_iff_disjoint_right.mpr hKL.symm
  intro T hT
  exact hLB T (rc24_traceCond_antitone hLKc hT)

open Classical in


theorem rc24_famCylBox_eq_complCylBox (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ = rc24_complCylBox 𝒜 ℬ :=
  Finset.Subset.antisymm (rc24_famCylBox_subset_complCylBox 𝒜 ℬ)
    (rc24_complCylBox_subset_famCylBox 𝒜 ℬ)


theorem rc24_upComp_eq_complConj (i : α) (𝒜 : Finset (Finset α)) :
    rc22_upComp i 𝒜 = (Down.compression i (𝒜.image compl)).image compl := by
  have hid : (𝒜.image compl).image compl = 𝒜 := by rw [Finset.image_image]; simp
  have h := rc22_complImage_downCompression i (𝒜.image compl)
  rw [hid] at h
  exact h.symm


end StatMech.Walls
