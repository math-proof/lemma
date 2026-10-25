/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc6hallavailable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc6deficitform.Part4
import Theorem.StatisticalMechanics.Code.Walls.rc2_hallavailable
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc6hallavailable
open Finset Function
open scoped StatMech


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in
@[simp] theorem rc6_mem_boxFinset {A B : Set (ConfigSpace α)} {ω : ConfigSpace α} :
    ω ∈ rc6_boxFinset A B ↔ ω ∈ disjointOccurrence A B := by
  simp only [rc6_boxFinset, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in
@[simp] theorem rc6_mem_imgFinset {A B : Set (ConfigSpace α)} {ω : ConfigSpace α} :
    ω ∈ rc6_imgFinset A B ↔ (ω ∈ A ∧ (fun a => !ω a) ∈ B) := by
  simp only [rc6_imgFinset, Finset.mem_filter, Finset.mem_univ, true_and]

open Classical in


theorem rc6_reimerCardForm_iff_card_le (A B : Set (ConfigSpace α)) :
    poc_ReimerCardForm A B ↔ #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B) :=
  Iff.rfl


theorem rc6_card_le_iff_embedding (A B : Set (ConfigSpace α)) :
    #(rc6_boxFinset A B) ≤ #(rc6_imgFinset A B) ↔
      Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) := by
  rw [← Fintype.card_coe (rc6_boxFinset A B), ← Fintype.card_coe (rc6_imgFinset A B)]
  exact ⟨Function.Embedding.nonempty_of_card_le,
    fun ⟨e⟩ => Fintype.card_le_of_embedding e⟩


theorem rc6_reimerCardForm_iff_embedding (A B : Set (ConfigSpace α)) :
    poc_ReimerCardForm A B ↔
      Nonempty (↥(rc6_boxFinset A B) ↪ ↥(rc6_imgFinset A B)) := by
  rw [rc6_reimerCardForm_iff_card_le, rc6_card_le_iff_embedding]


end StatMech.Walls
