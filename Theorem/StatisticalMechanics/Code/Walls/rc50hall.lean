/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc50hall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc49doubled.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc50_jointImage_inter_complKL (S K L : Finset α) :
    rc49_jointImage S K L ∩ (K ∪ L)ᶜ = S ∩ (K ∪ L)ᶜ := by
  ext a
  simp only [rc49_jointImage, Finset.mem_inter, Finset.mem_union, Finset.mem_compl,
    Finset.mem_union]
  tauto


theorem rc50_jointImage_involutive (S K L : Finset α) (hKL : Disjoint K L) :
    rc49_jointImage (rc49_jointImage S K L) K L = S := by
  ext a
  have hd : a ∈ K → a ∉ L := fun h => Finset.disjoint_left.mp hKL h
  simp only [rc49_jointImage, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
    Finset.mem_union]
  tauto


theorem rc50_jointImage_injective_of_fixed_witness (K L : Finset α) (hKL : Disjoint K L) :
    Function.Injective (fun S => rc49_jointImage S K L) := by
  intro S S' h
  have h1 := rc50_jointImage_involutive S K L hKL
  have h2 := rc50_jointImage_involutive S' K L hKL
  simp only at h
  rw [← h1, ← h2, h]


open Classical in


theorem rc50_jointImage_mem_neighbourhood {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}
    (hKL : Disjoint K L)
    (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
    rc49_jointImage S K L ∈ rc49_neighbourhood 𝒜 ℬ S := by
  rw [rc49_neighbourhood, Finset.mem_filter]
  exact ⟨rc49_jointImage_mem_reflInter hKL hKA hLB, K, L, hKL, hKA, hLB, rfl⟩

open Classical in


theorem rc50_block_hall {𝒜 ℬ : Finset (Finset α)} {W : Finset (Finset α)} {K L : Finset α}
    (hKL : Disjoint K L)
    (hW : ∀ S ∈ W, (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ)) :
    #W ≤ #(W.biUnion (rc49_neighbourhood 𝒜 ℬ)) := by
  refine Finset.card_le_card_of_injOn (fun S => rc49_jointImage S K L) ?_ ?_
  · intro S hS
    rw [Finset.mem_coe] at hS
    rw [Finset.mem_coe, Finset.mem_biUnion]
    obtain ⟨hKA, hLB⟩ := hW S hS
    exact ⟨S, hS, rc50_jointImage_mem_neighbourhood hKL hKA hLB⟩
  · intro S _ S' _ h
    exact rc50_jointImage_injective_of_fixed_witness K L hKL h


end StatMech.Walls
