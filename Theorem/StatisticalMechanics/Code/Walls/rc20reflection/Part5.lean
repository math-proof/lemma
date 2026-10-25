/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc20reflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc19doublecover.Part4
import Def.StatisticalMechanics.Code.Walls.rc20reflection.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc20_perSupportReflection_iff_famCylBoxResidue :
    rc20_PerSupportReflection ↔ rc20_FamCylBoxResidue := by
  constructor
  · intro h n 𝒜 ℬ
    obtain ⟨f, hinj, hmem⟩ := h n 𝒜 ℬ
    exact Finset.card_le_card_of_injOn f hmem hinj
  · intro h n 𝒜 ℬ
    by_cases hne : (rc20_famCylBox 𝒜 ℬ).Nonempty
    · have hle := h n 𝒜 ℬ
      have hemb : Nonempty ((rc20_famCylBox 𝒜 ℬ) ↪ (rc10_reflInter 𝒜 ℬ)) := by
        rw [← Fintype.card_coe, ← Fintype.card_coe (rc10_reflInter 𝒜 ℬ)] at hle
        exact Function.Embedding.nonempty_of_card_le hle
      obtain ⟨e⟩ := hemb
      have htne : (rc10_reflInter 𝒜 ℬ).Nonempty := by
        rw [← Finset.card_pos]; exact lt_of_lt_of_le (Finset.card_pos.mpr hne) (h n 𝒜 ℬ)
      obtain ⟨t0, ht0⟩ := htne
      refine ⟨fun S => if hS : S ∈ rc20_famCylBox 𝒜 ℬ then (e ⟨S, hS⟩).val else t0, ?_, ?_⟩
      · intro a ha b hb hab
        rw [Finset.mem_coe] at ha hb
        simp only [dif_pos ha, dif_pos hb] at hab
        have : (⟨a, ha⟩ : (rc20_famCylBox 𝒜 ℬ : Finset (Finset (Fin n)))) = ⟨b, hb⟩ :=
          e.injective (Subtype.ext hab)
        exact congrArg Subtype.val this
      · intro S hS
        simp only [dif_pos hS]
        exact (e ⟨S, hS⟩).property
    · exact ⟨id, fun a ha => by rw [Finset.mem_coe] at ha; exact absurd ⟨a, ha⟩ hne,
        fun S hS => absurd ⟨S, hS⟩ hne⟩


theorem rc20_perSupportReflection_iff_cylBoxReflInter :
    rc20_PerSupportReflection ↔ rc18_CylBoxReflInter :=
  rc20_perSupportReflection_iff_famCylBoxResidue.trans rc20_famCylBoxResidue_iff_cylBoxReflInter

open Classical in


theorem rc20_perSupportReflection_satisfiable_rbi :
    ∃ f : Finset (Fin 2) → Finset (Fin 2),
      Set.InjOn f (rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({∅, {1}, {0, 1}})
        : Set (Finset (Fin 2))) ∧
      ∀ S ∈ rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({∅, {1}, {0, 1}}),
        f S ∈ rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({∅, {1}, {0, 1}}) := by
  set 𝒜 : Finset (Finset (Fin 2)) := {∅, {0}, {1}} with h𝒜
  set ℬ : Finset (Finset (Fin 2)) := {∅, {1}, {0, 1}} with hℬ
  have hle := rc20_famCylBox_fin2 𝒜 ℬ
  by_cases hne : (rc20_famCylBox 𝒜 ℬ).Nonempty
  · have hemb : Nonempty ((rc20_famCylBox 𝒜 ℬ) ↪ (rc10_reflInter 𝒜 ℬ)) := by
      rw [← Fintype.card_coe, ← Fintype.card_coe (rc10_reflInter 𝒜 ℬ)] at hle
      exact Function.Embedding.nonempty_of_card_le hle
    obtain ⟨e⟩ := hemb
    have htne : (rc10_reflInter 𝒜 ℬ).Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (Finset.card_pos.mpr hne) hle
    obtain ⟨t0, ht0⟩ := htne
    refine ⟨fun S => if hS : S ∈ rc20_famCylBox 𝒜 ℬ then (e ⟨S, hS⟩).val else t0, ?_, ?_⟩
    · intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      simp only [dif_pos ha, dif_pos hb] at hab
      have : (⟨a, ha⟩ : (rc20_famCylBox 𝒜 ℬ : Finset (Finset (Fin 2)))) = ⟨b, hb⟩ :=
        e.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
    · intro S hS
      simp only [dif_pos hS]
      exact (e ⟨S, hS⟩).property
  · exact ⟨id, fun a ha => by rw [Finset.mem_coe] at ha; exact absurd ⟨a, ha⟩ hne,
      fun S hS => absurd ⟨S, hS⟩ hne⟩


open Classical in


theorem rc20_reimer_reflection :
    (rc20_FamCylBoxResidue ↔ rc18_CylBoxReflInter)
      ∧ (rc20_PerSupportReflection ↔ rc18_CylBoxReflInter)
      ∧ (∀ A B : Set (ConfigSpace (Fin 2)), rc19_DoubledReflection A B)
      ∧ (∀ A : Set (ConfigSpace α), rc19_DoubledReflection A (Set.univ : Set (ConfigSpace α)))
      ∧ (∀ B : Set (ConfigSpace α), rc19_DoubledReflection (Set.univ : Set (ConfigSpace α)) B)
      ∧ (∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (S : Finset (Fin 2)),
          S ∈ rc20_famCylBox 𝒜 ℬ ∧ S ∉ rc10_reflInter 𝒜 ℬ) :=
  ⟨rc20_famCylBoxResidue_iff_cylBoxReflInter,
    rc20_perSupportReflection_iff_cylBoxReflInter,
    rc20_doubledReflection_fin2,
    rc20_doubledReflection_right_univ,
    rc20_doubledReflection_left_univ,
    rc20_identityMirror_insufficient⟩

end StatMech.Walls
