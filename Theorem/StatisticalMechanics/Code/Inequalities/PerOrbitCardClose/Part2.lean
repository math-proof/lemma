/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
import Def.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part2
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem poc_card_boxOrbit (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    #(boxOrbit A B k) = #(poc_slabBox A B k) := by
  classical
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    simp only [boxOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hbox, hk⟩ := hp
    have h2 := poc_snd_eq p k hk
    simp only [poc_slabBox, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hbox, ?_⟩
    rw [show (p.1, poc_keyFlip k p.1) = p from Prod.ext rfl h2.symm]; exact hk
  · intro p hp q hq hpq
    simp only [boxOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have h2p := poc_snd_eq p k hp.2
    have h2q := poc_snd_eq q k hq.2
    exact Prod.ext hpq (by rw [h2p, h2q, hpq])
  · intro ω hω
    simp only [poc_slabBox, Finset.mem_filter, Finset.mem_univ, true_and] at hω
    refine ⟨(ω, poc_keyFlip k ω), ?_, rfl⟩
    simp only [boxOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hω.1, hω.2⟩


theorem poc_card_imgOrbit (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    #(imgOrbit A B k) = #(poc_slabImg A B k) := by
  classical
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    simp only [imgOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hA, hB, hk⟩ := hp
    have h2 := poc_snd_eq p k hk
    simp only [poc_slabImg, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hA, ?_, ?_⟩
    · rw [← h2]; exact hB
    · rw [show (p.1, poc_keyFlip k p.1) = p from Prod.ext rfl h2.symm]; exact hk
  · intro p hp q hq hpq
    simp only [imgOrbit, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have h2p := poc_snd_eq p k hp.2.2
    have h2q := poc_snd_eq q k hq.2.2
    exact Prod.ext hpq (by rw [h2p, h2q, hpq])
  · intro ω hω
    simp only [poc_slabImg, Finset.mem_filter, Finset.mem_univ, true_and] at hω
    refine ⟨(ω, poc_keyFlip k ω), ?_, rfl⟩
    simp only [imgOrbit, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hω.1, hω.2.1, hω.2.2⟩


end StatMech
