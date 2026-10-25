/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc5_reflectinvolution.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc5_reindextransfer
import Theorem.StatisticalMechanics.Code.Walls.rc5_doubledboxcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc5_dpairsmodular
import Theorem.StatisticalMechanics.Code.Walls.rc5_itercompcard
import Theorem.StatisticalMechanics.Code.Walls.rc5_nonvacuity
import Theorem.StatisticalMechanics.Code.Walls.rc2_core.Part3
import Def.StatisticalMechanics.Code.Walls.rc5_core
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


section Injection

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in


theorem rc5_core_reimerCardForm_of_injection {A B : Set (ConfigSpace α)}
    (h : rc5_BoxReflectInjection A B) : StatMech.poc_ReimerCardForm A B := by
  rw [rmr_reimerCardForm_iff_inter]
  obtain ⟨f, hinj, hmem⟩ := h
  apply Finset.card_le_card_of_injOn f
  · intro ω hω
    rw [Finset.mem_coe, Finset.mem_filter] at hω
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hmem ω hω.2⟩
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    exact hinj ha.2 hb.2 hab

open Classical in


theorem rc5_core_injection_of_reimerCardForm {A B : Set (ConfigSpace α)}
    (h : StatMech.poc_ReimerCardForm A B) : rc5_BoxReflectInjection A B := by
  rw [rmr_reimerCardForm_iff_inter] at h
  set s := Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B) with hs
  set t := Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B) with ht
  by_cases hsne : s.Nonempty
  · have hemb : Nonempty (s ↪ t) := by
      rw [← Fintype.card_coe s, ← Fintype.card_coe t] at h
      exact Function.Embedding.nonempty_of_card_le h
    obtain ⟨e⟩ := hemb
    have htne : t.Nonempty := by
      rw [← Finset.card_pos]
      exact lt_of_lt_of_le (Finset.card_pos.mpr hsne) h
    obtain ⟨t0, ht0⟩ := htne
    classical
    refine ⟨fun ω => if hω : ω ∈ s then (e ⟨ω, hω⟩).val else t0, ?_, ?_⟩
    · intro a ha b hb hab
      have ha' : a ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha⟩
      have hb' : b ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb⟩
      simp only [dif_pos ha', dif_pos hb'] at hab
      have : (⟨a, ha'⟩ : s) = ⟨b, hb'⟩ := e.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
    · intro ω hbox
      have hω : ω ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hbox⟩
      simp only [dif_pos hω]
      have hmem : (e ⟨ω, hω⟩).val ∈ t := (e ⟨ω, hω⟩).property
      have hmem' : (e ⟨ω, hω⟩).val ∈ A ∩ rmr_reflect B := by
        have hthis : (e ⟨ω, hω⟩).val ∈ Finset.univ.filter
            (fun ω : ConfigSpace α => ω ∈ A ∩ rmr_reflect B) := ht ▸ hmem
        exact (Finset.mem_filter.mp hthis).2
      exact hmem'
  · refine ⟨id, ?_, ?_⟩
    · intro a ha
      exact absurd ⟨a, by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha⟩⟩ hsne
    · intro ω hbox
      exact absurd ⟨ω, by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hbox⟩⟩ hsne


theorem rc5_core_injection_iff_reimerCardForm (A B : Set (ConfigSpace α)) :
    rc5_BoxReflectInjection A B ↔ StatMech.poc_ReimerCardForm A B :=
  ⟨rc5_core_reimerCardForm_of_injection, rc5_core_injection_of_reimerCardForm⟩

end Injection
end StatMech.Walls
