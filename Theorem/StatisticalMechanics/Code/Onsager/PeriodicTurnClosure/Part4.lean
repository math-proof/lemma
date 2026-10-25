/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part4


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

theorem ons_periodStateList_nodup (n r : ℕ) :
    (ons_periodStateList n r).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  exact Prod.mk.inj hij |>.2

theorem ons_mem_allPeriodStates_fst_le
    (n N : ℕ) (z : ℕ × Fin n)
    (hz : z ∈ ons_allPeriodStates n N) :
    z.1 ≤ N := by
  rw [ons_allPeriodStates, List.mem_flatMap] at hz
  obtain ⟨r, hr, hz⟩ := hz
  rw [ons_periodStateList, List.mem_ofFn] at hz
  obtain ⟨i, rfl⟩ := hz
  exact Nat.le_of_lt_succ (List.mem_range.mp hr)

theorem ons_allPeriodStates_nodup (n N : ℕ) :
    (ons_allPeriodStates n N).Nodup := by
  induction N with
  | zero =>
      simpa [ons_allPeriodStates] using ons_periodStateList_nodup n 0
  | succ N ih =>
      rw [ons_allPeriodStates, List.range_succ,
        List.flatMap_append]
      simp only [List.flatMap_singleton]
      apply List.Nodup.append (by simpa [ons_allPeriodStates] using ih)
        (ons_periodStateList_nodup n (N + 1))
      rw [List.disjoint_iff_ne]
      intro a ha b hb hab
      have ha' : a.1 ≤ N :=
        ons_mem_allPeriodStates_fst_le n N a (by
          simpa [ons_allPeriodStates] using ha)
      rw [ons_periodStateList, List.mem_ofFn] at hb
      obtain ⟨i, rfl⟩ := hb
      have := congrArg Prod.fst hab
      simp at this
      omega

@[simp] theorem ons_periodStateList_length (n r : ℕ) :
    (ons_periodStateList n r).length = n := by
  simp [ons_periodStateList]

@[simp] theorem ons_allPeriodStates_length (n N : ℕ) :
    (ons_allPeriodStates n N).length = (N + 1) * n := by
  simp [ons_allPeriodStates, List.length_flatMap]

theorem ons_periodicArcStates_nodup {n : ℕ}
    (N : ℕ) (imin imax : Fin n) :
    (ons_periodicArcStates N imin imax).Nodup := by
  apply List.Nodup.sublist
    ((List.take_sublist _ _).trans (List.drop_sublist _ _))
  exact ons_allPeriodStates_nodup n N

@[simp] theorem ons_periodicArcStates_length {n : ℕ}
    (N : ℕ) (hN : 1 ≤ N) (imin imax : Fin n) :
    (ons_periodicArcStates N imin imax).length =
      N * n + imax.val + 1 - imin.val := by
  rw [ons_periodicArcStates, List.length_take, List.length_drop,
    ons_allPeriodStates_length]
  rw [Nat.min_eq_left]
  rw [Nat.add_mul]
  omega

theorem ons_mem_periodicArcStates_fst_le {n : ℕ}
    (N : ℕ) (imin imax : Fin n) (z : ℕ × Fin n)
    (hz : z ∈ ons_periodicArcStates N imin imax) :
    z.1 ≤ N := by
  apply ons_mem_allPeriodStates_fst_le n N z
  exact List.Sublist.mem hz
    ((List.take_sublist _ _).trans (List.drop_sublist _ _))

end StatMech.Onsager
