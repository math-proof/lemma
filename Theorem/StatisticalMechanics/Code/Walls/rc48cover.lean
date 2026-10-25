/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc48cover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc47reimer.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc48_compl_mem_reflInter {𝒜 ℬ : Finset (Finset α)} {S : Finset α}
    (hS : S ∈ rc20_famCylBox 𝒜 ℬ) (hSc : Sᶜ ∈ 𝒜) :
    Sᶜ ∈ rc10_reflInter 𝒜 ℬ := by
  rw [rc20_mem_reflInter, compl_compl]
  exact ⟨hSc, rc47_famCylBox_subset_right 𝒜 ℬ hS⟩

open Classical in


theorem rc48_famCylBox_le_reflInter_of_complSubset (𝒜 ℬ : Finset (Finset α))
    (h : ∀ S ∈ rc20_famCylBox 𝒜 ℬ, Sᶜ ∈ 𝒜) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  refine Finset.card_le_card_of_injOn (fun S => Sᶜ) ?_ ?_
  · intro S hS
    rw [Finset.mem_coe] at hS
    exact rc48_compl_mem_reflInter hS (h S hS)
  · intro S _ S' _ hSS'
    have := congrArg (compl : Finset α → Finset α) hSS'
    rwa [compl_compl, compl_compl] at this


open Classical in


theorem rc48_reflInter_mono_left {𝒜 𝒜' ℬ : Finset (Finset α)} (h : 𝒜 ⊆ 𝒜') :
    rc10_reflInter 𝒜 ℬ ⊆ rc10_reflInter 𝒜' ℬ := by
  intro S hS
  rw [rc20_mem_reflInter] at hS ⊢
  exact ⟨h hS.1, hS.2⟩

open Classical in


theorem rc48_reflInter_mono_right {𝒜 ℬ ℬ' : Finset (Finset α)} (h : ℬ ⊆ ℬ') :
    rc10_reflInter 𝒜 ℬ ⊆ rc10_reflInter 𝒜 ℬ' := by
  intro S hS
  rw [rc20_mem_reflInter] at hS ⊢
  exact ⟨hS.1, h hS.2⟩


end StatMech.Walls
