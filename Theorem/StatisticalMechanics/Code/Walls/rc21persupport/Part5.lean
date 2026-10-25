/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc20reflection.Part5
import Def.StatisticalMechanics.Code.Walls.rc21persupport.Part4
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc21_symmDiffMirror_fin2_refuted :
    ((rc21_boxComp 2 ({∅, {0}, {1}}) ({{0}, {1}, {0, 1}})).biUnion
        (fun S => (rc21_symmWitComp 2 ({∅, {0}, {1}}) ({{0}, {1}, {0, 1}}) S).image
          (fun L => symmDiff S L))).card
      < (rc21_boxComp 2 ({∅, {0}, {1}}) ({{0}, {1}, {0, 1}})).card := by
  decide

open Classical in


theorem rc21_wall_holds_refuting_pair :
    #(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}))
      ≤ #(rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}})) :=
  rc20_famCylBox_fin2 _ _

open Classical in


theorem rc21_generalReflection_refuting_pair :
    ∃ f : Finset (Fin 2) → Finset (Fin 2),
      Set.InjOn f (rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}})
        : Set (Finset (Fin 2))) ∧
      ∀ S ∈ rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}),
        f S ∈ rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}) := by
  set 𝒜 : Finset (Finset (Fin 2)) := {∅, {0}, {1}} with h𝒜
  set ℬ : Finset (Finset (Fin 2)) := {{0}, {1}, {0, 1}} with hℬ
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


theorem rc21_reimer_persupport :
    (rc21_SymmDiffReflection → rc18_CylBoxReflInter)
      ∧ (∀ {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}, Disjoint K L →
          (∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜) →
          (∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) →
          symmDiff S L ∈ rc10_reflInter 𝒜 ℬ)
      ∧ (rc21_localReflSearch 2 ({∅, {0}, {1}}) ({{0}, {1}, {0, 1}}) = false)
      ∧ (#(rc20_famCylBox ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}))
          ≤ #(rc10_reflInter ({∅, {0}, {1}} : Finset (Finset (Fin 2))) ({{0}, {1}, {0, 1}}))) :=
  ⟨rc21_cylBoxReflInter_of_symmDiffReflection,
    fun hKL hKA hLB => rc21_symmDiff_mem_reflInter hKL hKA hLB,
    rc21_localReflSearch_fin2_refuted,
    rc21_wall_holds_refuting_pair⟩

end StatMech.Walls
