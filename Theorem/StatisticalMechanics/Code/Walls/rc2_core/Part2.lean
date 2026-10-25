/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc2_slabcardallisbridge
import Theorem.StatisticalMechanics.Code.Walls.rc2_slabimgeqinter.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc2_cardformiffinter
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
import Theorem.StatisticalMechanics.Code.Walls.rc2_doubledboxcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc2_blendpoint
import Def.StatisticalMechanics.Code.Walls.rc2_core
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc2_slabInjection_imp_slabCard {A B : Set (ConfigSpace α)} (h : SlabInjection A B) :
    poc_SlabCard A B := by
  rw [rc2_slabCard_iff_perKey]
  intro k
  obtain ⟨f, hinj, hmem⟩ := h k
  apply Finset.card_le_card_of_injOn f
  · intro ω hω
    rw [Finset.mem_coe, Finset.mem_filter] at hω
    obtain ⟨_, hbox, hslab⟩ := hω
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hmem ω hbox hslab⟩
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    exact hinj ⟨ha.2.1, ha.2.2⟩ ⟨hb.2.1, hb.2.2⟩ hab

open Classical in


theorem rc2_slabInjection_of_slabCard {A B : Set (ConfigSpace α)} (h : poc_SlabCard A B) :
    SlabInjection A B := by
  rw [rc2_slabCard_iff_perKey] at h
  intro k
  set s := Finset.univ.filter (fun ω : ConfigSpace α => ω ∈ disjointOccurrence A B ∧ ω ∈ rc2_slab k)
    with hs
  set t := Finset.univ.filter
    (fun ω : ConfigSpace α => ω ∈ A ∩ rc2_keyReflect k B ∧ ω ∈ rc2_slab k) with ht
  
  by_cases hsne : s.Nonempty
  · 
    have hcard : s.card ≤ t.card := h k
    have hemb : Nonempty (s ↪ t) := by
      rw [← Fintype.card_coe s, ← Fintype.card_coe t] at hcard
      exact Function.Embedding.nonempty_of_card_le hcard
    obtain ⟨e⟩ := hemb
    
    have htne : t.Nonempty := by
      rw [← Finset.card_pos]
      exact lt_of_lt_of_le (Finset.card_pos.mpr hsne) hcard
    obtain ⟨t0, ht0⟩ := htne
    classical
    refine ⟨fun ω => if hω : ω ∈ s then (e ⟨ω, hω⟩).val else t0, ?_, ?_⟩
    · intro a ha b hb hab
      have ha' : a ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha⟩
      have hb' : b ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb⟩
      simp only [dif_pos ha', dif_pos hb'] at hab
      have : (⟨a, ha'⟩ : s) = ⟨b, hb'⟩ := e.injective (Subtype.ext hab)
      exact congrArg Subtype.val this
    · intro ω hbox hslab
      have hω : ω ∈ s := by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hbox, hslab⟩
      simp only [dif_pos hω]
      have hmem : (e ⟨ω, hω⟩).val ∈ t := (e ⟨ω, hω⟩).property
      rw [Finset.mem_filter] at hmem
      exact hmem.2
  · 
    refine ⟨id, ?_, ?_⟩
    · intro a ha
      exact absurd ⟨a, by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha⟩⟩ hsne
    · intro ω hbox hslab
      exact absurd ⟨ω, by rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hbox, hslab⟩⟩ hsne


theorem rc2_slabInjection_iff (A B : Set (ConfigSpace α)) :
    SlabInjection A B ↔ poc_SlabCard A B :=
  ⟨rc2_slabInjection_imp_slabCard, rc2_slabInjection_of_slabCard⟩


end StatMech.Walls
