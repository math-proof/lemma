/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part2
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


lemma mem_boxDoubled (𝒜 ℬ : Finset (Finset α)) (U : Finset (α ⊕ α)) :
    U ∈ boxDoubled 𝒜 ℬ ↔ ∃ S ∈ 𝒜, ∃ T ∈ ℬ, Disjoint S T ∧ dbl S T = U := by
  unfold boxDoubled
  simp only [mem_image, mem_filter, mem_product, Prod.exists]
  constructor
  · rintro ⟨S, T, ⟨⟨hS, hT⟩, hd⟩, rfl⟩; exact ⟨S, hS, T, hT, hd, rfl⟩
  · rintro ⟨S, hS, T, hT, hd, rfl⟩; exact ⟨S, T, ⟨⟨hS, hT⟩, hd⟩, rfl⟩


theorem card_boxDoubled (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card := by
  unfold boxDoubled
  exact Finset.card_image_of_injOn (dbl_injOn _)


theorem boxFamily_eq_image_collapse_boxDoubled (𝒜 ℬ : Finset (Finset α)) :
    boxFamily 𝒜 ℬ = (boxDoubled 𝒜 ℬ).image (fun U => U.image (Sum.elim id id)) := by
  ext U
  simp only [mem_boxFamily, mem_image, mem_boxDoubled]
  constructor
  · rintro ⟨S, hS, T, hT, hd, rfl⟩
    exact ⟨dbl S T, ⟨S, hS, T, hT, hd, rfl⟩, image_collapse_dbl S T⟩
  · rintro ⟨V, ⟨S, hS, T, hT, hd, rfl⟩, rfl⟩
    exact ⟨S, hS, T, hT, hd, (image_collapse_dbl S T).symm⟩


theorem card_boxFamily_le_boxDoubled (𝒜 ℬ : Finset (Finset α)) :
    (boxFamily 𝒜 ℬ).card ≤ (boxDoubled 𝒜 ℬ).card := by
  rw [boxFamily_eq_image_collapse_boxDoubled]
  exact card_image_le


theorem card_boxDoubled_le_mul (𝒜 ℬ : Finset (Finset α)) :
    (boxDoubled 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card := by
  rw [card_boxDoubled]
  calc ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card
      ≤ (𝒜 ×ˢ ℬ).card := card_filter_le _ _
    _ = 𝒜.card * ℬ.card := card_product _ _


end StatMech
