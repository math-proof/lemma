/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.GetD
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Basic
import Def.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part5
set_option autoImplicit false


namespace WreathOrbits

variable {m n : ℕ}

lemma sortedRowSizes_length (S : Finset (Fin m × Fin n)) :
    (sortedRowSizes S).length = m := by
  simp [sortedRowSizes]

lemma sortedRowSizes_pairwise (S : Finset (Fin m × Fin n)) :
    (sortedRowSizes S).Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort ..

lemma sortedRowSizes_multiset_eq (S : Finset (Fin m × Fin n)) :
    ↑(sortedRowSizes S) = Finset.univ.val.map (rowSize S) :=
  Multiset.sort_eq ..

lemma sortedRowSizes_le (S : Finset (Fin m × Fin n)) (k : ℕ)
    (hk : k < (sortedRowSizes S).length) : (sortedRowSizes S)[k] ≤ n := by
  have hmem : (sortedRowSizes S)[k] ∈ (Finset.univ.val.map (rowSize S)) := by
    rw [← sortedRowSizes_multiset_eq]; exact Multiset.mem_coe.mpr (List.getElem_mem hk)
  rw [Multiset.mem_map] at hmem
  obtain ⟨i, -, heq⟩ := hmem
  rw [← heq]; exact rowSize_le S i

lemma getD_le_n (S : Finset (Fin m × Fin n)) (i : Fin m) :
    (sortedRowSizes S).getD i.val 0 ≤ n := by
  have hlen : i.val < (sortedRowSizes S).length := by
    rw [sortedRowSizes_length]; exact i.isLt
  rw [List.getD_eq_getElem _ 0 hlen]
  exact sortedRowSizes_le S i.val hlen

end WreathOrbits
