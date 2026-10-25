/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc42multiwitness.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc43_famCylBox_symm (𝒜 ℬ : Finset (Finset α)) :
    rc20_famCylBox 𝒜 ℬ = rc20_famCylBox ℬ 𝒜 := by
  ext S
  rw [rc20_famCylBox, rc20_famCylBox, Finset.mem_filter, Finset.mem_filter]
  refine and_congr_right (fun _ => ?_)
  constructor
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    exact ⟨L, K, hKL.symm, hLB, hKA⟩
  · rintro ⟨K, L, hKL, hKB, hLA⟩
    exact ⟨L, K, hKL.symm, hLA, hKB⟩

open Classical in


theorem rc43_reflInter_card_transpose (𝒜 ℬ : Finset (Finset α)) :
    #(rc10_reflInter 𝒜 ℬ) = #(rc10_reflInter ℬ 𝒜) := by
  apply Finset.card_bij (fun S _ => Sᶜ)
  · intro S hS
    rw [rc20_mem_reflInter] at hS
    rw [rc20_mem_reflInter, compl_compl]
    exact ⟨hS.2, hS.1⟩
  · intro S _ S' _ h
    have := congrArg (compl : Finset α → Finset α) h
    rwa [compl_compl, compl_compl] at this
  · intro T hT
    rw [rc20_mem_reflInter] at hT
    refine ⟨Tᶜ, ?_, by rw [compl_compl]⟩
    rw [rc20_mem_reflInter, compl_compl]
    exact ⟨hT.2, hT.1⟩


theorem rc43_cwits_compl (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    (rc42_cwits n 𝒜 ℬ S).image compl = rc42_cwits n ℬ 𝒜 S := by
  ext K
  simp only [Finset.mem_image, rc42_cwits, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨J, ⟨hJA, hJcB⟩, rfl⟩
    exact ⟨hJcB, by rw [compl_compl]; exact hJA⟩
  · rintro ⟨hKB, hKcA⟩
    exact ⟨Kᶜ, ⟨hKcA, by rw [compl_compl]; exact hKB⟩, by rw [compl_compl]⟩


theorem rc43_cwits_card_transpose (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    (rc42_cwits n 𝒜 ℬ S).card = (rc42_cwits n ℬ 𝒜 S).card := by
  rw [← rc43_cwits_compl n 𝒜 ℬ S]
  exact (Finset.card_image_of_injective _ compl_injective).symm


open Classical in


theorem rc43_hall_of_commonCoveringWitness (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hKA : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hKcB : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) :
    𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
  refine Finset.card_le_card_of_injOn (fun S => rc36_R0 S K Kᶜ) ?_ ?_
  · 
    intro S hS
    rw [Finset.mem_coe] at hS
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨S, hS, ?_⟩
    refine rc42_slice_subset_admCovering n 𝒜 ℬ
      (fun T hT => ⟨(rc20_traceClass_subset_iff n K T 𝒜).mpr (hKA T hT),
        (rc20_traceClass_subset_iff n Kᶜ T ℬ).mpr (hKcB T hT)⟩) hS ?_
    exact rc36_R0_mem_traceSlice 𝒜 ℬ disjoint_compl_right (hKA S hS) (hKcB S hS)
  · 
    intro S _ S' _ h
    exact rc40_R0_injOn_of_cover K Kᶜ disjoint_compl_right (by simp) h

open Classical in


theorem rc43_commonCoveringWitness_generalises_rc41 (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {𝒯 : Finset (Finset (Fin n))} {K : Finset (Fin n)}
    (hKA : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hKcB : ∀ S ∈ 𝒯, ∀ T : Finset (Fin n), T ∩ Kᶜ = S ∩ Kᶜ → T ∈ ℬ) :
    𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card :=
  rc43_hall_of_commonCoveringWitness n 𝒜 ℬ hKA hKcB


end StatMech.Walls
