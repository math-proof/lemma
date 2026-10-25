/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/YoungTableaux.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic


noncomputable section

open scoped Classical

open Finset

namespace YoungDiagram

theorem rowLen_eq_zero_of_colLen_le (μ : YoungDiagram) {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  by_contra h
  have hpos : 0 < μ.rowLen i := Nat.pos_of_ne_zero h
  have : (i, 0) ∈ μ := mem_iff_lt_rowLen.mpr hpos
  rw [mem_iff_lt_colLen] at this
  omega

lemma rowLen_antitone (μ : YoungDiagram) : Antitone μ.rowLen := by
  intro i j hij
  by_contra hc; push Not at hc
  have h1 : (j, μ.rowLen i) ∈ μ := mem_iff_lt_rowLen.mpr (by omega)
  have h2 : (i, μ.rowLen i) ∈ μ :=
    μ.isLowerSet (Prod.mk_le_mk.mpr ⟨hij, le_rfl⟩) h1
  rw [mem_iff_lt_rowLen] at h2; omega

lemma rowLen_gt_of_lt_addable (μ : YoungDiagram) {i : ℕ}
    (hadd : i = 0 ∨ μ.rowLen (i - 1) > μ.rowLen i) {c : ℕ} (hc : c < i) :
    μ.rowLen c > μ.rowLen i := by
  rcases hadd with rfl | h
  · omega
  · exact lt_of_lt_of_le h (rowLen_antitone μ (by omega))

end YoungDiagram
end
