/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc25doubledcover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc24countbridge.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Def.StatisticalMechanics.Code.Walls.rc25doubledcover
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc25_box_le_dpairs (𝒜 ℬ : Finset (Finset α)) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ dpairsCount 𝒜 ℬ := by
  rw [rc24_famCylBox_eq_complCylBox, dpairsCount]
  apply Finset.card_le_card_of_injOn
    (fun S => (S ∩ rc25_witness 𝒜 ℬ S, S ∩ (rc25_witness 𝒜 ℬ S)ᶜ))
  · intro S hS
    simp only [Finset.mem_coe] at hS
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    dsimp only
    have hmem := (rc24_mem_complCylBox 𝒜 ℬ S).mp hS
    have hspec := Classical.choose_spec ((rc24_mem_complCylBox 𝒜 ℬ S).mp hS)
    have hw : rc25_witness 𝒜 ℬ S = Classical.choose hmem := by
      rw [rc25_witness]; rw [dif_pos hS]
    rw [hw]
    obtain ⟨hKA, hKcB⟩ := hspec
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact hKA (S ∩ Classical.choose hmem) (by rw [Finset.inter_assoc, Finset.inter_self])
    · exact hKcB (S ∩ (Classical.choose hmem)ᶜ) (by rw [Finset.inter_assoc, Finset.inter_self])
    · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right disjoint_compl_right)
  · intro S _ S' _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have eS : S ∩ rc25_witness 𝒜 ℬ S ∪ S ∩ (rc25_witness 𝒜 ℬ S)ᶜ = S := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    have eS' : S' ∩ rc25_witness 𝒜 ℬ S' ∪ S' ∩ (rc25_witness 𝒜 ℬ S')ᶜ = S' := by
      rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]
    rw [← eS, ← eS', h1, h2]


open Classical in


theorem rc25_witness_partition (𝒜 ℬ : Finset (Finset α)) (S : Finset α) :
    (S ∩ rc25_witness 𝒜 ℬ S) ∪ (S ∩ (rc25_witness 𝒜 ℬ S)ᶜ) = S := by
  rw [← Finset.inter_union_distrib_left, Finset.union_compl, Finset.inter_univ]


end StatMech.Walls
