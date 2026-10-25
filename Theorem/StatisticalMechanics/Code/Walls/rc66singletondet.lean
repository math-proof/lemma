/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc66singletondet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc65marriagetwo.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


open Classical in


theorem rc66_mem_nbhd (𝒜 ℬ : Finset (Finset (Fin n))) (S R : Finset (Fin n)) :
    R ∈ rc59_nbhd 𝒜 ℬ S ↔
      R ∈ 𝒜 ∧ Rᶜ ∈ ℬ ∧
        ∃ K : Finset (Fin n), (∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜) ∧ R ∩ K = S ∩ K := by
  rw [rc59_nbhd_eq_admOneSidedA, rc33_admOneSidedA, Finset.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨_, hRA, hRB, K, _, hKA, hRK⟩
    exact ⟨hRA, hRB, K, (rc20_traceClass_subset_iff n K S 𝒜).mp hKA, hRK⟩
  · rintro ⟨hRA, hRB, K, hKA, hRK⟩
    exact ⟨Finset.mem_univ _, hRA, hRB, K, Finset.mem_univ _,
      (rc20_traceClass_subset_iff n K S 𝒜).mpr hKA, hRK⟩


open Classical in


theorem rc66_self_mem_nbhd (𝒜 ℬ : Finset (Finset (Fin n))) {S : Finset (Fin n)}
    (hbox : S ∈ rc20_famCylBox 𝒜 ℬ) (hRI : S ∈ rc10_reflInter 𝒜 ℬ) :
    S ∈ rc59_nbhd 𝒜 ℬ S := by
  rw [rc20_famCylBox, Finset.mem_filter] at hbox
  obtain ⟨_, K, L, _hKL, hKA, _hLB⟩ := hbox
  rw [rc20_mem_reflInter] at hRI
  rw [rc66_mem_nbhd]
  exact ⟨hRI.1, hRI.2, K, hKA, rfl⟩

open Classical in


theorem rc66_singleton_nbhd_forces_self (𝒜 ℬ : Finset (Finset (Fin n))) {S R : Finset (Fin n)}
    (hbox : S ∈ rc20_famCylBox 𝒜 ℬ) (hRI : S ∈ rc10_reflInter 𝒜 ℬ)
    (hnb : rc59_nbhd 𝒜 ℬ S = {R}) : R = S := by
  have hself := rc66_self_mem_nbhd 𝒜 ℬ hbox hRI
  rw [hnb, Finset.mem_singleton] at hself
  exact hself.symm

open Classical in


theorem rc66_singletonInjective_on_reflInter (𝒜 ℬ : Finset (Finset (Fin n)))
    {S₁ S₂ : Finset (Fin n)}
    (hbox₁ : S₁ ∈ rc20_famCylBox 𝒜 ℬ) (hRI₁ : S₁ ∈ rc10_reflInter 𝒜 ℬ)
    (hbox₂ : S₂ ∈ rc20_famCylBox 𝒜 ℬ) (hRI₂ : S₂ ∈ rc10_reflInter 𝒜 ℬ)
    (hne : S₁ ≠ S₂) (R : Finset (Fin n))
    (hR₁ : rc59_nbhd 𝒜 ℬ S₁ = {R}) (hR₂ : rc59_nbhd 𝒜 ℬ S₂ = {R}) : False := by
  have h1 := rc66_singleton_nbhd_forces_self 𝒜 ℬ hbox₁ hRI₁ hR₁
  have h2 := rc66_singleton_nbhd_forces_self 𝒜 ℬ hbox₂ hRI₂ hR₂
  exact hne (h1.symm.trans h2)


open Classical in


theorem rc66_marriageTwoPair_on_reflInter (𝒜 ℬ : Finset (Finset (Fin n)))
    {S₁ S₂ : Finset (Fin n)}
    (hbox₁ : S₁ ∈ rc20_famCylBox 𝒜 ℬ) (hRI₁ : S₁ ∈ rc10_reflInter 𝒜 ℬ)
    (hbox₂ : S₂ ∈ rc20_famCylBox 𝒜 ℬ) (hRI₂ : S₂ ∈ rc10_reflInter 𝒜 ℬ)
    (hne : S₁ ≠ S₂) : rc65_MarriageTwoPair 𝒜 ℬ S₁ S₂ := by
  classical
  by_cases hbig : 2 ≤ (rc59_nbhd 𝒜 ℬ S₁).card ∨ 2 ≤ (rc59_nbhd 𝒜 ℬ S₂).card
  · exact rc65_marriage_two_of_nbhd_card_ge_two 𝒜 ℬ S₁ S₂ hbig
  · rw [not_or, Nat.not_le, Nat.not_le] at hbig
    obtain ⟨hb1, hb2⟩ := hbig
    have h1ne := rc65_nbhd_nonempty 𝒜 ℬ hbox₁
    have h2ne := rc65_nbhd_nonempty 𝒜 ℬ hbox₂
    have hc1 : (rc59_nbhd 𝒜 ℬ S₁).card = 1 :=
      le_antisymm (Nat.lt_succ_iff.mp hb1) h1ne.card_pos
    have hc2 : (rc59_nbhd 𝒜 ℬ S₂).card = 1 :=
      le_antisymm (Nat.lt_succ_iff.mp hb2) h2ne.card_pos
    obtain ⟨R₁, hR₁⟩ := Finset.card_eq_one.mp hc1
    obtain ⟨R₂, hR₂⟩ := Finset.card_eq_one.mp hc2
    by_cases hRR : R₁ = R₂
    · subst hRR
      exact (rc66_singletonInjective_on_reflInter 𝒜 ℬ hbox₁ hRI₁ hbox₂ hRI₂ hne R₁ hR₁ hR₂).elim
    · refine rc65_marriage_two_of_nbhd_ne 𝒜 ℬ h1ne h2ne ?_
      rw [hR₁, hR₂]; simpa using hRR

open Classical in


theorem rc66_singletonInjective_fin2 (𝒜 ℬ : Finset (Finset (Fin 2)))
    {S₁ S₂ : Finset (Fin 2)} (hS₁ : S₁ ∈ rc20_famCylBox 𝒜 ℬ) (hS₂ : S₂ ∈ rc20_famCylBox 𝒜 ℬ)
    (hne : S₁ ≠ S₂) (R : Finset (Fin 2))
    (hR₁ : rc59_nbhd 𝒜 ℬ S₁ = {R}) (hR₂ : rc59_nbhd 𝒜 ℬ S₂ = {R}) : False :=
  rc65_singletonInjective_fin2 𝒜 ℬ hS₁ hS₂ hne R hR₁ hR₂


end StatMech.Walls
