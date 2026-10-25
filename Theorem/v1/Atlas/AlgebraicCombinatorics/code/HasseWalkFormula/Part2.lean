/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalkFormula.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.NormalOrderCoeff.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.NormalOrderCoeff
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.HasseWalks
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountOps
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountBridge
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkOperatorLemmas
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.HasseWalks
import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkCountOps
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkCountBridge.Part2
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkOperatorLemmas
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Combinatorics.Young.YoungDiagram
import Def.v1.Atlas.AlgebraicCombinatorics.code.HasseWalkFormula.Part2
set_option autoImplicit false

open scoped Nat


lemma HasseWalkFormula.upWalkType_cells_subset {m : ℕ} {mu : YoungDiagram}
    (w : Fin (m + 1) → YoungDiagram)
    (_h0 : w ⟨0, Nat.zero_lt_succ _⟩ = ⊥)
    (hs : ∀ i : Fin m, w ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
      w ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    (he : w ⟨m, Nat.lt_succ_of_le le_rfl⟩ = mu)
    (k : Fin (m + 1)) : (w k).cells ⊆ mu.cells := by
  obtain ⟨k, hk⟩ := k
  have hle : ∀ (i : ℕ) (hi : i < m + 1) (j : ℕ) (hj : j < m + 1),
      i ≤ j → (w ⟨i, hi⟩).cells ⊆ (w ⟨j, hj⟩).cells := by
    intro i hi j hj hij
    induction hij with
    | refl => exact Finset.Subset.refl _
    | step _ ih =>
      rename_i j' _
      exact Finset.Subset.trans (ih (by omega)) ((hs ⟨j', by omega⟩).lt.le)
  have : (w ⟨k, hk⟩).cells ⊆ (w ⟨m, Nat.lt_succ_of_le le_rfl⟩).cells :=
    hle k hk m (Nat.lt_succ_of_le le_rfl) (by omega)
  rw [he] at this; exact this

