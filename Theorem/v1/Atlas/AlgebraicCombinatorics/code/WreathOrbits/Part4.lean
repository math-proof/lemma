module
public import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.List.GetD
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Logic.Equiv.Basic
public import Def.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits.Part5
set_option autoImplicit false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
