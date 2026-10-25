/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc11bkriffincinc
import Theorem.StatisticalMechanics.Code.Walls.rc11boxsuppupper
import Theorem.StatisticalMechanics.Code.Walls.rc11reflinterstructure
import Theorem.StatisticalMechanics.Code.Walls.rc11doublecoverrepresentation
import Theorem.StatisticalMechanics.Code.Walls.rc11compressionengine
import Def.StatisticalMechanics.Code.Walls.rc11core
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc11_card_le_of_injection {𝒜 ℬ : Finset (Finset α)} (h : rc11_BKRInjection 𝒜 ℬ) :
    #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) := by
  obtain ⟨f, hinj, hmem⟩ := h
  exact Finset.card_le_card_of_injOn f hmem hinj

open Classical in


theorem rc11_injection_of_card_le {𝒜 ℬ : Finset (Finset α)}
    (h : #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ)) : rc11_BKRInjection 𝒜 ℬ := by
  by_cases hne : (rc10_boxSupp 𝒜 ℬ).Nonempty
  · have hemb : Nonempty ((rc10_boxSupp 𝒜 ℬ) ↪ (rc10_reflInter 𝒜 ℬ)) := by
      rw [← Fintype.card_coe, ← Fintype.card_coe] at h
      exact Function.Embedding.nonempty_of_card_le h
    obtain ⟨e⟩ := hemb
    have htne : (rc10_reflInter 𝒜 ℬ).Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (Finset.card_pos.mpr hne) h
    obtain ⟨t0, _⟩ := htne
    refine ⟨fun S => if hS : S ∈ rc10_boxSupp 𝒜 ℬ then (e ⟨S, hS⟩).val else t0, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe] at ha hb
      simp only [dif_pos ha, dif_pos hb] at hab
      have : (⟨a, ha⟩ : rc10_boxSupp 𝒜 ℬ) = ⟨b, hb⟩ := e.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
    · intro S hS
      simp only [dif_pos hS]; exact (e ⟨S, hS⟩).property
  · exact ⟨id, fun a ha => absurd ⟨a, Finset.mem_coe.mp ha⟩ hne, fun S hS => absurd ⟨S, hS⟩ hne⟩


theorem rc11_injection_iff_card_le (𝒜 ℬ : Finset (Finset α)) :
    rc11_BKRInjection 𝒜 ℬ ↔ #(rc10_boxSupp 𝒜 ℬ) ≤ #(rc10_reflInter 𝒜 ℬ) :=
  ⟨rc11_card_le_of_injection, rc11_injection_of_card_le⟩


end StatMech.Walls
