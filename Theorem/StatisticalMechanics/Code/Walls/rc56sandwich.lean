/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc56sandwich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc55nonproduct.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc47reimer.Part3
import Instance.StatisticalMechanics.Code.Walls.rc56sandwich
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc56_mem_famCylBox_iff_witness (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    S ∈ rc20_famCylBox 𝒜 ℬ ↔ rc56_hasWitness 𝒜 ℬ S :=
  rc21_mem_famCylBox 𝒜 ℬ S

omit [Fintype α] in


theorem rc56_mem_inter_of_hasWitness (𝒜 ℬ : Finset (Finset α)) {S : Finset α}
    (h : rc56_hasWitness 𝒜 ℬ S) : S ∈ 𝒜 ∩ ℬ := by
  obtain ⟨K, L, _, hKA, hLB⟩ := h
  rw [Finset.mem_inter]
  exact ⟨hKA S rfl, hLB S rfl⟩

open Classical in


theorem rc56_famCylBox_eq_inter_filter (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ = (𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ) := by
  ext S
  rw [Finset.mem_filter, rc56_mem_famCylBox_iff_witness]
  constructor
  · intro h
    exact ⟨rc56_mem_inter_of_hasWitness 𝒜 ℬ h, h⟩
  · intro h
    exact h.2

open Classical in


theorem rc56_famCylBox_card_eq_witnessCount (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) = #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) := by
  rw [rc56_famCylBox_eq_inter_filter]


open Classical in


theorem rc56_famCylBox_symm (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜 := by
  ext S
  rw [rc56_mem_famCylBox_iff_witness, rc56_mem_famCylBox_iff_witness]
  constructor
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    exact ⟨L, K, hKL.symm, hLB, hKA⟩
  · rintro ⟨K, L, hKL, hKB, hLA⟩
    exact ⟨L, K, hKL.symm, hLA, hKB⟩

open Classical in


theorem rc56_famCylBox_card_symm (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) = #(rc20_famCylBox ℬ 𝒜) := by
  rw [rc56_famCylBox_symm]

open Classical in


theorem rc56_reflInter_card_symm (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜) := by
  refine Finset.card_bij (fun S _ => Sᶜ) ?_ ?_ ?_
  · intro S hS
    rw [rc20_mem_reflInter] at hS
    rw [rc20_mem_reflInter, compl_compl]
    exact ⟨hS.2, hS.1⟩
  · intro S _ S' _ h
    have := congrArg (compl : Finset α → Finset α) h
    rwa [compl_compl, compl_compl] at this
  · intro R hR
    rw [rc20_mem_reflInter] at hR
    refine ⟨Rᶜ, ?_, compl_compl R⟩
    rw [rc20_mem_reflInter, compl_compl]
    exact ⟨hR.2, hR.1⟩


open Classical in


theorem rc56_reflInter_card_eq_interComplFam (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) = #(𝒜 ∩ rc22_complFam ℬ) := by
  rw [rc22_reflInter_eq_inter_complFam]

open Classical in


theorem rc56_wall_iff_witnessedInter (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔
      #((𝒜 ∩ ℬ).filter (rc56_hasWitness 𝒜 ℬ)) ≤ #(𝒜 ∩ rc22_complFam ℬ) := by
  rw [rc56_famCylBox_card_eq_witnessCount, rc56_reflInter_card_eq_interComplFam]


end StatMech.Walls
