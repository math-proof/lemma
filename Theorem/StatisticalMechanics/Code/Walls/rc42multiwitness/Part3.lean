/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc42multiwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc41hall.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
import Def.StatisticalMechanics.Code.Walls.rc42multiwitness.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc42_admCovering_subset_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) : rc42_admCovering n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S := by
  intro R hR
  rw [rc42_admCovering, Finset.mem_biUnion] at hR
  obtain ⟨K, hK, hRslice⟩ := hR
  rw [rc42_cwits, Finset.mem_filter] at hK
  exact rc35_slice_subset_admOneSidedA n 𝒜 ℬ
    ((rc20_traceClass_subset_iff n K S 𝒜).mp hK.2.1) hRslice

open Classical in


theorem rc42_admCovering_nonempty_of_mem_box (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S : Finset (Fin n)} (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    (rc42_admCovering n 𝒜 ℬ S).Nonempty := by
  obtain ⟨K, L, hKL, hcov, hKA, hLB⟩ := rc40_coveringPair_of_mem_box n 𝒜 ℬ hS
  
  have hLKc : L = Kᶜ := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_compl]
      exact Finset.disjoint_right.mp hKL hx
    · intro x hx
      rw [Finset.mem_compl] at hx
      have : x ∈ K ∪ L := hcov ▸ Finset.mem_univ x
      rcases Finset.mem_union.mp this with h | h
      · exact absurd h hx
      · exact h
  have hKcw : K ∈ rc42_cwits n 𝒜 ℬ S := by
    rw [rc42_cwits, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, (rc20_traceClass_subset_iff n K S 𝒜).mpr hKA, ?_⟩
    rw [← hLKc]
    exact (rc20_traceClass_subset_iff n L S ℬ).mpr hLB
  refine ⟨rc36_R0 S K L, ?_⟩
  rw [rc42_admCovering, Finset.mem_biUnion]
  exact ⟨K, hKcw, rc36_R0_mem_traceSlice 𝒜 ℬ hKL hKA hLB⟩


end StatMech.Walls
