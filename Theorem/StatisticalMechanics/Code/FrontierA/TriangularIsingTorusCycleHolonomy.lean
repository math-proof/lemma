/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleHolonomy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSurfaceTwist
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy
open scoped BigOperators


namespace StatMech.FrontierA

open scoped Affine


@[simp] theorem triangularIntPos_zero {n : Nat} [NeZero n]
    (direction : Fin n -> Fin 6) :
    triangularIntPos direction 0 = 0 := by
  have hzero : Finset.univ.filter (· < (0 : Fin n)) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro i _
    exact Fin.not_lt_zero i
  rw [triangularIntPos, hzero, Finset.sum_empty]


theorem triangularIntPos_succ {n : Nat} [NeZero n]
    (direction : Fin n -> Fin 6)
    (hclosed : ∑ i, triangularIntStep (direction i) = 0)
    (k : Fin n) :
    triangularIntPos direction (k + 1) =
      triangularIntPos direction k + triangularIntStep (direction k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  by_cases hk : k = Fin.last m
  · have hzero : (k + 1 : Fin (m + 1)) = 0 := by
      apply Fin.ext
      rw [Fin.val_add_one, if_pos hk]
      rfl
    have hfilter : Finset.univ.filter (· < k) =
        Finset.univ.erase k := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, and_true]
      constructor
      · exact fun hi => ne_of_lt hi
      · intro hne
        have hik : i ≤ k := by
          rw [hk]
          exact Fin.le_last i
        exact lt_of_le_of_ne hik hne
    rw [hzero, triangularIntPos_zero]
    have hpos : triangularIntPos direction k =
        ∑ i ∈ Finset.univ.erase k,
          triangularIntStep (direction i) := by
      rw [triangularIntPos, hfilter]
    rw [hpos, add_comm]
    rw [Finset.add_sum_erase Finset.univ
      (fun i => triangularIntStep (direction i))
      (Finset.mem_univ k)]
    exact hclosed.symm
  · have hval : ((k + 1 : Fin (m + 1)) : Nat) = k.val + 1 := by
      rw [Fin.val_add_one, if_neg hk]
    have hfilter : Finset.univ.filter (· < (k + 1)) =
        insert k (Finset.univ.filter (· < k)) := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert]
      constructor
      · intro hi
        rw [Fin.lt_def, hval] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
        · exact Or.inr (Fin.lt_def.2 hlt)
        · exact Or.inl (Fin.ext heq)
      · intro hi
        rw [Fin.lt_def, hval]
        rcases hi with rfl | hlt
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (Fin.lt_def.1 hlt)
    have hnotmem : k ∉ Finset.univ.filter (· < k) := by
      simp [Finset.mem_filter]
    rw [triangularIntPos, hfilter, Finset.sum_insert hnotmem, add_comm]
    rw [triangularIntPos]


end StatMech.FrontierA
