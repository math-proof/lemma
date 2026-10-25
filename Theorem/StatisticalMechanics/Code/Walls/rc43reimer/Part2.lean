/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc43reimer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc42multiwitness.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Def.StatisticalMechanics.Code.Walls.rc43reimer
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc43_hallCovering_of_globalCommonWitness (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : rc43_GlobalCommonWitness n 𝒜 ℬ) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc42_admCovering n 𝒜 ℬ)).card := by
  obtain ⟨K, hKA, hKcB⟩ := h
  intro 𝒯 h𝒯
  rw [Finset.mem_powerset] at h𝒯
  exact rc43_hall_of_commonCoveringWitness n 𝒜 ℬ
    (fun S hS => hKA S (h𝒯 hS)) (fun S hS => hKcB S (h𝒯 hS))

open Classical in


theorem rc43_famCylBox_le_reflInter_of_globalCommonWitness (n : ℕ)
    (𝒜 ℬ : Finset (Finset (Fin n))) (h : rc43_GlobalCommonWitness n 𝒜 ℬ) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  have hHall := rc43_hallCovering_of_globalCommonWitness n 𝒜 ℬ h
    (rc20_famCylBox 𝒜 ℬ) (Finset.mem_powerset.mpr (Finset.Subset.refl _))
  refine hHall.trans (Finset.card_le_card ?_)
  intro R hR
  rw [Finset.mem_biUnion] at hR
  obtain ⟨S, _, hRS⟩ := hR
  exact rc33_admOneSidedA_subset_reflInter n 𝒜 ℬ S
    (rc42_admCovering_subset_admOneSidedA n 𝒜 ℬ S hRS)


end StatMech.Walls
