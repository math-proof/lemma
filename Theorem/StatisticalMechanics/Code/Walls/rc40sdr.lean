/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc40sdr.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc36hallmarriage.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc37doubledhall.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] in


theorem rc40_L_sdiff_R0 (S K L : Finset α) (hKL : Disjoint K L) :
    L \ rc36_R0 S K L = S ∩ L := by
  rw [rc36_R0]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, not_or]
  constructor
  · rintro ⟨hxL, hnot⟩
    refine ⟨?_, hxL⟩
    by_contra hxS
    exact hnot.2 ⟨hxL, hxS⟩
  · rintro ⟨hxS, hxL⟩
    refine ⟨hxL, ?_, ?_⟩
    · rintro ⟨_, hxK⟩; exact Finset.disjoint_right.mp hKL hxL hxK
    · rintro ⟨_, hxnS⟩; exact hxnS hxS

omit [Fintype α] in


theorem rc40_R0_recovers_covered (S K L : Finset α) (hKL : Disjoint K L) :
    (rc36_R0 S K L ∩ K) ∪ (L \ rc36_R0 S K L) = S ∩ (K ∪ L) := by
  rw [rc36_R0_inter_left S K L hKL, rc40_L_sdiff_R0 S K L hKL, Finset.inter_union_distrib_left]


theorem rc40_R0_recovers_of_cover (S K L : Finset α) (hKL : Disjoint K L) (hcov : K ∪ L = univ) :
    (rc36_R0 S K L ∩ K) ∪ (L \ rc36_R0 S K L) = S := by
  rw [rc40_R0_recovers_covered S K L hKL, hcov, Finset.inter_univ]


theorem rc40_R0_injOn_of_cover (K L : Finset α) (hKL : Disjoint K L) (hcov : K ∪ L = univ)
    {S S' : Finset α} (h : rc36_R0 S K L = rc36_R0 S' K L) : S = S' := by
  have hS := rc40_R0_recovers_of_cover S K L hKL hcov
  have hS' := rc40_R0_recovers_of_cover S' K L hKL hcov
  rw [← hS, ← hS', h]


theorem rc40_coveringPair_of_mem_box (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S : Finset (Fin n)} (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    ∃ K L : Finset (Fin n), Disjoint K L ∧ K ∪ L = univ ∧
      (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧
      (∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) := by
  rw [rc20_famCylBox, Finset.mem_filter] at hS
  obtain ⟨_, K, L₀, hKL₀, hKA, hL₀B⟩ := hS
  refine ⟨K, Kᶜ, disjoint_compl_right, ?_, hKA, ?_⟩
  · rw [Finset.union_compl]
  · 
    have hL₀sub : L₀ ⊆ Kᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      exact Finset.disjoint_right.mp hKL₀ hx
    have hL₀wit : L₀ ∈ rc35_awitsA n ℬ S := by
      rw [rc35_awitsA, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (rc20_traceClass_subset_iff n L₀ S ℬ).mpr hL₀B⟩
    have hKcwit : Kᶜ ∈ rc35_awitsA n ℬ S :=
      rc36_awitsA_upward_closed n ℬ S hL₀wit hL₀sub
    rw [rc35_awitsA, Finset.mem_filter] at hKcwit
    exact (rc20_traceClass_subset_iff n Kᶜ S ℬ).mp hKcwit.2


theorem rc40_R0_cover_mem_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S : Finset (Fin n)} (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    ∃ K L : Finset (Fin n), Disjoint K L ∧ K ∪ L = univ ∧
      rc36_R0 S K L ∈ rc33_admOneSidedA n 𝒜 ℬ S ∧
      (rc36_R0 S K L ∩ K) ∪ (L \ rc36_R0 S K L) = S := by
  obtain ⟨K, L, hKL, hcov, hKA, hLB⟩ := rc40_coveringPair_of_mem_box n 𝒜 ℬ hS
  exact ⟨K, L, hKL, hcov, rc36_R0_mem_admOneSidedA n 𝒜 ℬ hKL hKA hLB,
    rc40_R0_recovers_of_cover S K L hKL hcov⟩


end StatMech.Walls
