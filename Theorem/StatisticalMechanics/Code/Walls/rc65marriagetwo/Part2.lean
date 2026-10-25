/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc65marriagetwo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc64consolidation.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc41hall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc40sdr.Part3
import Def.StatisticalMechanics.Code.Walls.rc65marriagetwo
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


open Classical in


theorem rc65_marriage_two_of_nbhd_card_ge_two (𝒜 ℬ : Finset (Finset (Fin n)))
    (S₁ S₂ : Finset (Fin n))
    (h : 2 ≤ (rc59_nbhd 𝒜 ℬ S₁).card ∨ 2 ≤ (rc59_nbhd 𝒜 ℬ S₂).card) :
    rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
  rcases h with h | h
  · exact h.trans (Finset.card_le_card Finset.subset_union_left)
  · exact h.trans (Finset.card_le_card Finset.subset_union_right)

open Classical in


theorem rc65_marriage_two_of_nbhd_ne (𝒜 ℬ : Finset (Finset (Fin n)))
    {S₁ S₂ : Finset (Fin n)}
    (h1 : (rc59_nbhd 𝒜 ℬ S₁).Nonempty) (h2 : (rc59_nbhd 𝒜 ℬ S₂).Nonempty)
    (hne : rc59_nbhd 𝒜 ℬ S₁ ≠ rc59_nbhd 𝒜 ℬ S₂) :
    rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
  rw [rc65_MarriageTwoPair, show (2 : ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff,
    Finset.one_lt_card_iff]
  
  obtain ⟨x, hx⟩ : ∃ x, (x ∈ rc59_nbhd 𝒜 ℬ S₁ ∧ x ∉ rc59_nbhd 𝒜 ℬ S₂) ∨
      (x ∈ rc59_nbhd 𝒜 ℬ S₂ ∧ x ∉ rc59_nbhd 𝒜 ℬ S₁) := by
    rw [Ne, Finset.ext_iff, not_forall] at hne
    obtain ⟨x, hx⟩ := hne
    refine ⟨x, ?_⟩
    by_cases h1 : x ∈ rc59_nbhd 𝒜 ℬ S₁
    · exact Or.inl ⟨h1, fun h2 => hx (iff_of_true h1 h2)⟩
    · have h2 : x ∈ rc59_nbhd 𝒜 ℬ S₂ := by
        by_contra h2
        exact hx (iff_of_false h1 h2)
      exact Or.inr ⟨h2, h1⟩
  rcases hx with ⟨hxS1, hxS2⟩ | ⟨hxS2, hxS1⟩
  · obtain ⟨y, hy⟩ := h2
    exact ⟨x, y, Finset.mem_union_left _ hxS1, Finset.mem_union_right _ hy,
      fun h => hxS2 (h ▸ hy)⟩
  · obtain ⟨y, hy⟩ := h1
    exact ⟨x, y, Finset.mem_union_right _ hxS2, Finset.mem_union_left _ hy,
      fun h => hxS1 (h ▸ hy)⟩

open Classical in


theorem rc65_marriage_two_of_commonWitness (𝒜 ℬ : Finset (Finset (Fin n)))
    {S₁ S₂ K : Finset (Fin n)}
    (hKA₁ : ∀ T : Finset (Fin n), T ∩ K = S₁ ∩ K → T ∈ 𝒜)
    (hKA₂ : ∀ T : Finset (Fin n), T ∩ K = S₂ ∩ K → T ∈ 𝒜)
    (hKcB₁ : ∀ T : Finset (Fin n), T ∩ Kᶜ = S₁ ∩ Kᶜ → T ∈ ℬ)
    (hKcB₂ : ∀ T : Finset (Fin n), T ∩ Kᶜ = S₂ ∩ Kᶜ → T ∈ ℬ)
    (htrace : S₁ ∩ K ≠ S₂ ∩ K) :
    rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
  
  have hr₁ : rc36_R0 S₁ K Kᶜ ∈ rc59_nbhd 𝒜 ℬ S₁ := by
    rw [rc59_nbhd_eq_admOneSidedA]
    exact rc41_R0cover_mem_admOneSidedA n 𝒜 ℬ hKA₁ hKcB₁
  have hr₂ : rc36_R0 S₂ K Kᶜ ∈ rc59_nbhd 𝒜 ℬ S₂ := by
    rw [rc59_nbhd_eq_admOneSidedA]
    exact rc41_R0cover_mem_admOneSidedA n 𝒜 ℬ hKA₂ hKcB₂
  have hrne : rc36_R0 S₁ K Kᶜ ≠ rc36_R0 S₂ K Kᶜ := by
    intro h
    exact htrace (rc41_R0cover_traceEq S₁ S₂ K h)
  rw [rc65_MarriageTwoPair, show (2 : ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff,
    Finset.one_lt_card_iff]
  exact ⟨rc36_R0 S₁ K Kᶜ, rc36_R0 S₂ K Kᶜ, Finset.mem_union_left _ hr₁,
    Finset.mem_union_right _ hr₂, hrne⟩


end StatMech.Walls
