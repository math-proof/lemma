/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Inequalities.ReimerDoubled
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


@[simp] lemma mem_dbl_inl (S T : Finset α) (a : α) : (Sum.inl a) ∈ dbl S T ↔ a ∈ S := by
  simp [dbl, Finset.mem_union, Finset.mem_map]


@[simp] lemma mem_dbl_inr (S T : Finset α) (a : α) : (Sum.inr a) ∈ dbl S T ↔ a ∈ T := by
  simp [dbl, Finset.mem_union, Finset.mem_map]


lemma mem_dbl (S T : Finset α) (x : α ⊕ α) :
    x ∈ dbl S T ↔ Sum.elim (· ∈ S) (· ∈ T) x := by
  cases x with
  | inl a => simp [mem_dbl_inl S T a]
  | inr a => simp [mem_dbl_inr S T a]


lemma dbl_injective : Function.Injective (fun p : Finset α × Finset α => dbl p.1 p.2) := by
  rintro ⟨S, T⟩ ⟨S', T'⟩ h
  simp only at h
  have hS : S = S' := by ext a; rw [← mem_dbl_inl S T a, ← mem_dbl_inl S' T' a, h]
  have hT : T = T' := by ext a; rw [← mem_dbl_inr S T a, ← mem_dbl_inr S' T' a, h]
  rw [hS, hT]


lemma dbl_injOn (s : Set (Finset α × Finset α)) :
    Set.InjOn (fun p : Finset α × Finset α => dbl p.1 p.2) s :=
  dbl_injective.injOn


lemma image_collapse_dbl (S T : Finset α) :
    (dbl S T).image (Sum.elim id id) = S ∪ T := by
  ext a
  simp only [dbl, Finset.mem_image, Finset.mem_union, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨x, hx, rfl⟩
    cases x with
    | inl s => rcases hx with (⟨s', hs', h⟩ | ⟨t', ht', h⟩) <;> simp_all
    | inr t => rcases hx with (⟨s', hs', h⟩ | ⟨t', ht', h⟩) <;> simp_all
  · rintro (ha | ha)
    · exact ⟨Sum.inl a, Or.inl ⟨a, ha, rfl⟩, rfl⟩
    · exact ⟨Sum.inr a, Or.inr ⟨a, ha, rfl⟩, rfl⟩


end StatMech
