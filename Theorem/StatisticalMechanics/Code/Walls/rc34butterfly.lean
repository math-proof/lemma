/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc34butterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc33nonlocal.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc34_reflInter_symmDiff_mem_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S K L : Finset (Fin n)} (hKL : Disjoint K L)
    (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) :
    symmDiff S L ∈ rc33_admOneSidedA n 𝒜 ℬ S := by
  have hmem := rc21_symmDiff_mem_reflInter hKL hKA hLB
  rw [rc20_mem_reflInter] at hmem
  rw [rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq]
  refine ⟨Finset.mem_univ _, hmem.1, hmem.2, K, Finset.mem_univ _, ?_, ?_⟩
  · exact (rc20_traceClass_subset_iff n K S 𝒜).mpr hKA
  · exact rc21_symmDiff_inter_left S K L hKL

open Classical in


theorem rc34_self_mem_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    {S K : Finset (Fin n)} (hSRI : S ∈ rc10_reflInter 𝒜 ℬ)
    (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) :
    S ∈ rc33_admOneSidedA n 𝒜 ℬ S := by
  rw [rc20_mem_reflInter] at hSRI
  rw [rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq]
  exact ⟨Finset.mem_univ _, hSRI.1, hSRI.2, K, Finset.mem_univ _,
    (rc20_traceClass_subset_iff n K S 𝒜).mpr hKA, rfl⟩


open Classical in


theorem rc34_admComp_subset_admOneSidedA (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) :
    rc21_admComp n 𝒜 ℬ S ⊆ rc33_admOneSidedA n 𝒜 ℬ S := by
  intro R hR
  rw [rc21_admComp, Finset.mem_filter, decide_eq_true_eq] at hR
  obtain ⟨_, K, _, L, _, _, hKA, hLB, hRK, hRL⟩ := hR
  have hKA' : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜 :=
    (rc20_traceClass_subset_iff n K S 𝒜).mp hKA
  have hLB' : ∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ :=
    (rc20_traceClass_subset_iff n L S ℬ).mp hLB
  have hmem := rc21_localRefl_mem_reflInter hKA' hLB' hRK hRL
  rw [rc20_mem_reflInter] at hmem
  rw [rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq]
  exact ⟨Finset.mem_univ _, hmem.1, hmem.2, K, Finset.mem_univ _, hKA, hRK⟩


theorem rc34_hall_of_subgraph {β : Type*} [DecidableEq β] (𝒢 : Finset (Finset β))
    (t t' : Finset β → Finset (Finset β)) (hsub : ∀ S ∈ 𝒢, t S ⊆ t' S)
    (hHall : ∀ 𝒯 ∈ 𝒢.powerset, 𝒯.card ≤ (𝒯.biUnion t).card) :
    ∀ 𝒯 ∈ 𝒢.powerset, 𝒯.card ≤ (𝒯.biUnion t').card := by
  intro 𝒯 h𝒯
  rw [Finset.mem_powerset] at h𝒯
  refine le_trans (hHall 𝒯 (Finset.mem_powerset.mpr h𝒯)) ?_
  exact Finset.card_le_card (Finset.biUnion_mono (fun S hS => hsub S (h𝒯 hS)))

open Classical in


theorem rc34_hallOneSidedA_of_localReflHall (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n)))
    (hHall : ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc21_admComp n 𝒜 ℬ)).card) :
    ∀ 𝒯 ∈ (rc20_famCylBox 𝒜 ℬ).powerset,
      𝒯.card ≤ (𝒯.biUnion (rc33_admOneSidedA n 𝒜 ℬ)).card :=
  rc34_hall_of_subgraph (rc20_famCylBox 𝒜 ℬ) (rc21_admComp n 𝒜 ℬ) (rc33_admOneSidedA n 𝒜 ℬ)
    (fun S _ => rc34_admComp_subset_admOneSidedA n 𝒜 ℬ S) hHall


end StatMech.Walls
