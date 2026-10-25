/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc19doublecover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc18nonmono.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Def.StatisticalMechanics.Code.Walls.rc19doublecover.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc19_cylBoxReflInter_of_doubledReflection {A B : Set (ConfigSpace α)}
    (h : rc19_DoubledReflection A B) :
    #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) := by
  obtain ⟨f, hinj, hmem⟩ := h
  exact Finset.card_le_card_of_injOn f hmem hinj

open Classical in


theorem rc19_doubledReflection_of_cylBoxReflInter {A B : Set (ConfigSpace α)}
    (h : #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B))) :
    rc19_DoubledReflection A B := by
  by_cases hne : (rc18_cylBoxSupp A B).Nonempty
  · have hemb : Nonempty ((rc18_cylBoxSupp A B) ↪ (rc10_reflInter (eventFamily A) (eventFamily B))) := by
      rw [← Fintype.card_coe, ← Fintype.card_coe (rc10_reflInter (eventFamily A) (eventFamily B))] at h
      exact Function.Embedding.nonempty_of_card_le h
    obtain ⟨e⟩ := hemb
    have htne : (rc10_reflInter (eventFamily A) (eventFamily B)).Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (Finset.card_pos.mpr hne) h
    obtain ⟨t0, ht0⟩ := htne
    refine ⟨fun S => if hS : S ∈ rc18_cylBoxSupp A B then (e ⟨S, hS⟩).val else t0, ?_, ?_⟩
    · intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      simp only [dif_pos ha, dif_pos hb] at hab
      have : (⟨a, ha⟩ : (rc18_cylBoxSupp A B : Finset (Finset α))) = ⟨b, hb⟩ :=
        e.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
    · intro S hS
      simp only [dif_pos hS]
      exact (e ⟨S, hS⟩).property
  · refine ⟨id, ?_, ?_⟩
    · intro a ha; rw [Finset.mem_coe] at ha; exact absurd ⟨a, ha⟩ hne
    · intro S hS; exact absurd ⟨S, hS⟩ hne


theorem rc19_doubledReflection_iff_card (A B : Set (ConfigSpace α)) :
    rc19_DoubledReflection A B ↔
      #(rc18_cylBoxSupp A B) ≤ #(rc10_reflInter (eventFamily A) (eventFamily B)) :=
  ⟨rc19_cylBoxReflInter_of_doubledReflection, rc19_doubledReflection_of_cylBoxReflInter⟩


end StatMech.Walls
