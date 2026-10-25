/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc65marriagetwo.Part3
import Def.StatisticalMechanics.Code.Walls.rc66singletondet
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem rc66_witness_box :
    ({0} : Finset (Fin 2)) ∈ rc20_famCylBox rc66_wA rc66_wB ∧
      (∅ : Finset (Fin 2)) ∈ rc20_famCylBox rc66_wA rc66_wB ∧
      ({0} : Finset (Fin 2)) ≠ (∅ : Finset (Fin 2)) := by
  refine ⟨?_, ?_, by decide⟩
  · rw [← rc21_boxComp_eq]; decide
  · rw [← rc21_boxComp_eq]; decide


theorem rc66_witness_offReflInter :
    ({0} : Finset (Fin 2)) ∉ rc10_reflInter rc66_wA rc66_wB := by
  rw [rc20_mem_reflInter]; decide


theorem rc66_witness_sharedNeighbour :
    (∅ : Finset (Fin 2)) ∈ rc59_nbhd rc66_wA rc66_wB {0} ∧
      (∅ : Finset (Fin 2)) ∈ rc59_nbhd rc66_wA rc66_wB (∅ : Finset (Fin 2)) := by
  rw [rc59_nbhd_eq_admOneSidedA, rc59_nbhd_eq_admOneSidedA]
  exact ⟨by decide, by decide⟩


theorem rc66_witness_singleton_broken :
    rc59_nbhd rc66_wA rc66_wB {0} = {∅} ∧
      rc59_nbhd rc66_wA rc66_wB (∅ : Finset (Fin 2)) ≠ {∅} := by
  rw [rc59_nbhd_eq_admOneSidedA, rc59_nbhd_eq_admOneSidedA]
  exact ⟨by decide, by decide⟩


open Classical in


theorem rc66_status :
    
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) {S R : Finset (Fin m)},
        S ∈ rc20_famCylBox 𝒜 ℬ → S ∈ rc10_reflInter 𝒜 ℬ →
        rc59_nbhd 𝒜 ℬ S = {R} → R = S) ∧
    (∀ (m : ℕ) (𝒜 ℬ : Finset (Finset (Fin m))) {S₁ S₂ : Finset (Fin m)},
        S₁ ∈ rc20_famCylBox 𝒜 ℬ → S₁ ∈ rc10_reflInter 𝒜 ℬ →
        S₂ ∈ rc20_famCylBox 𝒜 ℬ → S₂ ∈ rc10_reflInter 𝒜 ℬ → S₁ ≠ S₂ →
        ∀ R : Finset (Fin m), rc59_nbhd 𝒜 ℬ S₁ = {R} → rc59_nbhd 𝒜 ℬ S₂ = {R} → False) ∧
    
    (∀ (𝒜 ℬ : Finset (Finset (Fin 2))) {S₁ S₂ : Finset (Fin 2)},
        S₁ ∈ rc20_famCylBox 𝒜 ℬ → S₂ ∈ rc20_famCylBox 𝒜 ℬ → S₁ ≠ S₂ →
        ∀ R : Finset (Fin 2), rc59_nbhd 𝒜 ℬ S₁ = {R} → rc59_nbhd 𝒜 ℬ S₂ = {R} → False) ∧
    
    (({0} : Finset (Fin 2)) ∈ rc20_famCylBox rc66_wA rc66_wB ∧
      (∅ : Finset (Fin 2)) ∈ rc20_famCylBox rc66_wA rc66_wB ∧
      ({0} : Finset (Fin 2)) ≠ (∅ : Finset (Fin 2))) ∧
    ((∅ : Finset (Fin 2)) ∈ rc59_nbhd rc66_wA rc66_wB {0} ∧
      (∅ : Finset (Fin 2)) ∈ rc59_nbhd rc66_wA rc66_wB (∅ : Finset (Fin 2))) ∧
    (rc59_nbhd rc66_wA rc66_wB {0} = {∅} ∧
      rc59_nbhd rc66_wA rc66_wB (∅ : Finset (Fin 2)) ≠ {∅}) :=
  ⟨fun _m 𝒜 ℬ {_S _R} hbox hRI hnb => rc66_singleton_nbhd_forces_self 𝒜 ℬ hbox hRI hnb,
   fun _m 𝒜 ℬ {_S₁ _S₂} hb₁ hRI₁ hb₂ hRI₂ hne R hR₁ hR₂ =>
     rc66_singletonInjective_on_reflInter 𝒜 ℬ hb₁ hRI₁ hb₂ hRI₂ hne R hR₁ hR₂,
   fun 𝒜 ℬ {_S₁ _S₂} hS₁ hS₂ hne R hR₁ hR₂ =>
     rc66_singletonInjective_fin2 𝒜 ℬ hS₁ hS₂ hne R hR₁ hR₂,
   rc66_witness_box, rc66_witness_sharedNeighbour, rc66_witness_singleton_broken⟩

end StatMech.Walls
