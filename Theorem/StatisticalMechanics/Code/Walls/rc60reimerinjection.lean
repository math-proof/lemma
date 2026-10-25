/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc60reimerinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc59doubledcover.Part5
import Mathlib.Combinatorics.SetFamily.Compression.Down
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc60_nbhd_eq (𝒜 ℬ : Finset (Finset (Fin n))) (S : Finset (Fin n)) :
    rc59_nbhd 𝒜 ℬ S = rc33_admOneSidedA n 𝒜 ℬ S :=
  rc59_nbhd_eq_admOneSidedA 𝒜 ℬ S


open Classical in

theorem rc60_indepHall_empty (𝒜 ℬ : Finset (Finset (Fin n))) :
    (∅ : Finset (Finset (Fin n))).card
      ≤ ((∅ : Finset (Finset (Fin n))).biUnion (rc59_nbhd 𝒜 ℬ)).card := by
  simp

open Classical in


theorem rc60_indepHall_singleton (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S ∈ rc20_famCylBox 𝒜 ℬ) :
    ({S} : Finset (Finset (Fin n))).card
      ≤ (({S} : Finset (Finset (Fin n))).biUnion (rc59_nbhd 𝒜 ℬ)).card := by
  rw [Finset.card_singleton, Finset.singleton_biUnion, rc59_nbhd_eq_admOneSidedA]
  exact (rc36_admOneSidedA_nonempty_of_mem_box n 𝒜 ℬ hS).card_pos


open Classical in


theorem rc60_self_mem_nbhd_of_reflInter (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hS : S ∈ rc10_reflInter 𝒜 ℬ) : S ∈ rc59_nbhd 𝒜 ℬ S := by
  rw [rc59_nbhd_eq_admOneSidedA, rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq]
  rw [rc20_mem_reflInter] at hS
  refine ⟨Finset.mem_univ _, hS.1, hS.2, univ, Finset.mem_univ _, ?_, rfl⟩
  
  intro T hT
  rw [rc20_traceClass, Finset.mem_filter] at hT
  have : T = S := by
    have h := hT.2
    rwa [Finset.inter_univ, Finset.inter_univ] at h
  rw [this]; exact hS.1


open Classical in


theorem rc60_biUnion_nbhd_subset_reflInter (𝒜 ℬ : Finset (Finset (Fin n)))
    (𝒯 : Finset (Finset (Fin n))) :
    𝒯.biUnion (rc59_nbhd 𝒜 ℬ) ⊆ rc10_reflInter 𝒜 ℬ := by
  intro R hR
  rw [Finset.mem_biUnion] at hR
  obtain ⟨S, _, hRS⟩ := hR
  rw [rc59_nbhd_eq_admOneSidedA] at hRS
  exact rc33_admOneSidedA_subset_reflInter n 𝒜 ℬ S hRS

open Classical in


theorem rc60_wall_of_boxUnionBound (𝒜 ℬ : Finset (Finset (Fin n)))
    (h : #(rc20_famCylBox 𝒜 ℬ)
      ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  h.trans (Finset.card_le_card (rc60_biUnion_nbhd_subset_reflInter 𝒜 ℬ _))

open Classical in


theorem rc60_boxUnionBound_of_indepHall (h : rc59_IndepHall) (m : ℕ)
    (𝒜 ℬ : Finset (Finset (Fin m))) :
    #(rc20_famCylBox 𝒜 ℬ) ≤ #((rc20_famCylBox 𝒜 ℬ).biUnion (rc59_nbhd 𝒜 ℬ)) :=
  h m 𝒜 ℬ (rc20_famCylBox 𝒜 ℬ) (Finset.mem_powerset.mpr (Finset.Subset.refl _))


end StatMech.Walls
