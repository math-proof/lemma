/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Mathlib.Data.Finset.Prod
import Def.StatisticalMechanics.Code.Inequalities.ReimerStep.Part2
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


theorem downCompressFamily_eq_self_of_isDownAt (i : α) {𝒜 : Finset (Finset α)}
    (h : IsDownAtCoord i 𝒜) : Down.compression i 𝒜 = 𝒜 := by
  ext s
  rw [Down.mem_compression]
  constructor
  · rintro (⟨hs, _⟩ | ⟨hns, hins⟩)
    · exact hs
    · by_cases hi : i ∈ s
      · rw [insert_eq_of_mem hi] at hins; exact absurd hins hns
      · have := h _ hins; rw [erase_insert hi] at this; exact absurd this hns
  · intro hs; exact Or.inl ⟨hs, h _ hs⟩


theorem boxFamily_downCompress_eq_of_isDownAt (i : α) {𝒜 ℬ : Finset (Finset α)}
    (h𝒜 : IsDownAtCoord i 𝒜) (hℬ : IsDownAtCoord i ℬ) :
    boxFamily (Down.compression i 𝒜) (Down.compression i ℬ) = boxFamily 𝒜 ℬ := by
  rw [downCompressFamily_eq_self_of_isDownAt i h𝒜,
      downCompressFamily_eq_self_of_isDownAt i hℬ]


end StatMech
