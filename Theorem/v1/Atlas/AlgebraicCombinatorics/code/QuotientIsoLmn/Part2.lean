/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QuotientIsoLmn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part5
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WreathOrbits
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Def.v1.Atlas.AlgebraicCombinatorics.code.QuotientIsoLmn.Part3
set_option autoImplicit false
set_option maxHeartbeats 800000

open WreathOrbits YoungLattice YoungLattice.Lmn


namespace QuotientIsoLmn

variable {m n : ℕ}

lemma gridYoungToLmn_lmnToGridYoung (p : Lmn m n) :
    gridYoungToLmn (lmnToGridYoung p) = p := by
  apply Lmn.ext; intro i; simp only [gridYoungToLmn, lmnToGridYoung]
  ext; exact lmnToFinset_rowSize p i

lemma lmnToGridYoung_gridYoungToLmn (S : GridYoungDiagram m n) :
    lmnToGridYoung (gridYoungToLmn S) = S := by
  apply Subtype.ext; ext ⟨i, j⟩
  show (i, j) ∈ lmnToFinset (gridYoungToLmn S) ↔ (i, j) ∈ S.val
  rw [mem_lmnToFinset]; exact (WreathOrbits.mem_iff_lt_rowSize S.property.1 i j).symm

lemma rowSize_le_of_subset {S T : Finset (Fin m × Fin n)}
    (hST : S ⊆ T) (i : Fin m) :
    WreathOrbits.rowSize S i ≤ WreathOrbits.rowSize T i := by
  unfold WreathOrbits.rowSize; apply Finset.card_le_card
  intro x hx; simp only [Finset.mem_filter] at hx ⊢; exact ⟨hST hx.1, hx.2⟩

lemma gridYoungToLmn_le_iff (S T : GridYoungDiagram m n) :
    gridYoungToLmn S ≤ gridYoungToLmn T ↔ S ≤ T := by
  constructor
  · intro h; show S.val ⊆ T.val; intro ⟨i, j⟩ hmem
    rw [WreathOrbits.mem_iff_lt_rowSize S.property.1 i j] at hmem
    rw [WreathOrbits.mem_iff_lt_rowSize T.property.1 i j]
    exact lt_of_lt_of_le hmem (h i)
  · intro h i; exact rowSize_le_of_subset h i

end QuotientIsoLmn
