/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc19doublecover.Part4
import Def.StatisticalMechanics.Code.Walls.rc20reflection.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc20_traceClass_subset_iff (n : ℕ) (K S : Finset (Fin n)) (𝒜 : Finset (Finset (Fin n))) :
    rc20_traceClass n K S ⊆ 𝒜 ↔ ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜 := by
  rw [rc20_traceClass]
  constructor
  · intro h T hT
    exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩)
  · intro h T hT
    rw [Finset.mem_filter] at hT
    exact h T hT.2

open Classical in

theorem rc20_famCylBoxComp_eq (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc20_famCylBoxComp n 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ := by
  ext S
  rw [rc20_famCylBoxComp, rc20_famCylBox, Finset.mem_filter, Finset.mem_filter, decide_eq_true_eq]
  refine and_congr_right (fun _ => ?_)
  constructor
  · rintro ⟨K, _, L, _, hKL, hKA, hLB⟩
    exact ⟨K, L, hKL, (rc20_traceClass_subset_iff n K S 𝒜).mp hKA,
      (rc20_traceClass_subset_iff n L S ℬ).mp hLB⟩
  · rintro ⟨K, L, hKL, hKA, hLB⟩
    exact ⟨K, Finset.mem_univ _, L, Finset.mem_univ _, hKL,
      (rc20_traceClass_subset_iff n K S 𝒜).mpr hKA, (rc20_traceClass_subset_iff n L S ℬ).mpr hLB⟩

open Classical in

theorem rc20_reflInterComp_eq (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    rc20_reflInterComp n 𝒜 ℬ = rc10_reflInter 𝒜 ℬ := by
  ext S
  rw [rc20_reflInterComp, rc10_reflInter, Finset.mem_filter, Finset.mem_filter, decide_eq_true_eq]


theorem rc20_famCylBox_card_le_iff_comp (n : ℕ) (𝒜 ℬ : Finset (Finset (Fin n))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) ↔
      (rc20_famCylBoxComp n 𝒜 ℬ).card ≤ (rc20_reflInterComp n 𝒜 ℬ).card := by
  rw [rc20_famCylBoxComp_eq, rc20_reflInterComp_eq]


theorem rc20_famCylBox_fin0 (𝒜 ℬ : Finset (Finset (Fin 0))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rw [rc20_famCylBox_card_le_iff_comp]
  revert 𝒜 ℬ
  decide


theorem rc20_famCylBox_fin1 (𝒜 ℬ : Finset (Finset (Fin 1))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rw [rc20_famCylBox_card_le_iff_comp]
  revert 𝒜 ℬ
  decide

set_option maxHeartbeats 4000000 in


theorem rc20_famCylBox_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  rw [rc20_famCylBox_card_le_iff_comp]
  revert 𝒜 ℬ
  decide


open Classical in


theorem rc20_cylBoxReflInter_fin2 (A B : Set (ConfigSpace (Fin 2))) :
    #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
  rw [rc20_cylBoxSupp_eq_famCylBox A B]
  exact rc20_famCylBox_fin2 (eventFamily A) (eventFamily B)

open Classical in


theorem rc20_doubledReflection_fin2 (A B : Set (ConfigSpace (Fin 2))) :
    rc19_DoubledReflection A B :=
  rc19_doubledReflection_of_cylBoxReflInter (rc20_cylBoxReflInter_fin2 A B)

open Classical in

theorem rc20_doubledReflection_fin1 (A B : Set (ConfigSpace (Fin 1))) :
    rc19_DoubledReflection A B := by
  apply rc19_doubledReflection_of_cylBoxReflInter
  rw [rc20_cylBoxSupp_eq_famCylBox A B]
  exact rc20_famCylBox_fin1 (eventFamily A) (eventFamily B)

open Classical in

theorem rc20_doubledReflection_fin0 (A B : Set (ConfigSpace (Fin 0))) :
    rc19_DoubledReflection A B := by
  apply rc19_doubledReflection_of_cylBoxReflInter
  rw [rc20_cylBoxSupp_eq_famCylBox A B]
  exact rc20_famCylBox_fin0 (eventFamily A) (eventFamily B)


open Classical in


theorem rc20_identityMirror_insufficient :
    ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (S : Finset (Fin 2)),
      S ∈ rc20_famCylBox 𝒜 ℬ ∧ S ∉ rc10_reflInter 𝒜 ℬ := by
  refine ⟨{∅, {0}, {1}}, {∅, {1}, {0, 1}}, {1}, ?_, ?_⟩
  · rw [← rc20_famCylBoxComp_eq]; decide
  · rw [← rc20_reflInterComp_eq]; decide


open Classical in


theorem rc20_famCylBox_mono_left {𝒜 𝒜' ℬ : Finset (Finset α)} (h : 𝒜 ⊆ 𝒜') :
    rc20_famCylBox 𝒜 ℬ ⊆ rc20_famCylBox 𝒜' ℬ := by
  intro S hS
  rw [rc20_famCylBox, Finset.mem_filter] at hS ⊢
  obtain ⟨_, K, L, hKL, hKA, hLB⟩ := hS
  exact ⟨Finset.mem_univ _, K, L, hKL, fun T hT => h (hKA T hT), hLB⟩

open Classical in


theorem rc20_famCylBox_mono_right {𝒜 ℬ ℬ' : Finset (Finset α)} (h : ℬ ⊆ ℬ') :
    rc20_famCylBox 𝒜 ℬ ⊆ rc20_famCylBox 𝒜 ℬ' := by
  intro S hS
  rw [rc20_famCylBox, Finset.mem_filter] at hS ⊢
  obtain ⟨_, K, L, hKL, hKA, hLB⟩ := hS
  exact ⟨Finset.mem_univ _, K, L, hKL, hKA, fun T hT => h (hLB T hT)⟩


open Classical in


theorem rc20_famCylBox_of_increasing {n : ℕ} {A B : Set (ConfigSpace (Fin n))}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    #(rc20_famCylBox (eventFamily A) (eventFamily B))
      ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
  rw [← rc20_cylBoxSupp_eq_famCylBox A B]
  exact rc18_cylBoxReflInter_of_bkr hA hB


open Classical in


theorem rc20_doubledReflection_rbi :
    ((¬ IsIncreasing rbi_B ∧ ¬ IsDecreasing rbi_B))
      ∧ rc19_DoubledReflection rbi_A rbi_B :=
  ⟨⟨rc17_rbiB_not_increasing, rc17_rbiB_not_decreasing⟩, rc20_doubledReflection_fin2 rbi_A rbi_B⟩


end StatMech.Walls
