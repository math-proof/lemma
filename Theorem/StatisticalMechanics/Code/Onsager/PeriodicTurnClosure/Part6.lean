/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part6


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

@[simp] theorem ons_periodStateList_getLast? {n : ℕ} [NeZero n]
    (r : ℕ) :
    (ons_periodStateList n r).getLast? =
      some (r, ons_lastFin n) := by
  change (List.ofFn (fun i : Fin n ↦ (r, i))).getLast? = _
  rw [List.getLast?_eq_some_getLast (by
    simpa using (NeZero.ne n))]
  rw [List.getLast_ofFn (by
    simpa using (NeZero.ne n))]
  congr 2

@[simp] theorem ons_allPeriodStates_getLast? {n : ℕ} [NeZero n]
    (N : ℕ) :
    (ons_allPeriodStates n N).getLast? =
      some (N, ons_lastFin n) := by
  rw [ons_allPeriodStates, List.range_succ, List.flatMap_append]
  simp

theorem ons_allPeriodStates_isChain {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) :
    List.IsChain
      (fun a b ↦ ons_periodStateCoord d b =
        ons_periodStateCoord d a + stepOf (d a.2))
      (ons_allPeriodStates n N) := by
  induction N with
  | zero =>
      simpa [ons_allPeriodStates] using ons_periodStateList_isChain d 0
  | succ N ih =>
      rw [ons_allPeriodStates, List.range_succ,
        List.flatMap_append]
      simp only [List.flatMap_singleton]
      apply List.IsChain.append
        (by simpa [ons_allPeriodStates] using ih)
        (ons_periodStateList_isChain d (N + 1))
      intro a ha b hb
      have ha' : a = (N, ons_lastFin n) := by
        change a ∈ (ons_allPeriodStates n N).getLast? at ha
        have := ha
        rw [ons_allPeriodStates_getLast?] at this
        symm
        simpa using this
      have hb' : b = (N + 1, (0 : Fin n)) := by
        change b ∈ (ons_periodStateList n (N + 1)).head? at hb
        have := hb
        rw [ons_periodStateList_head?] at this
        symm
        simpa using this
      rw [ha', hb']
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
      change ons_periodStateCoord d (N + 1, 0) =
        ons_periodStateCoord d (N, Fin.last m) +
          stepOf (d (Fin.last m))
      exact ons_periodState_boundary d N

theorem ons_periodicArcStates_isChain {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (imin imax : Fin n) :
    List.IsChain
      (fun a b ↦ ons_periodStateCoord d b =
        ons_periodStateCoord d a + stepOf (d a.2))
      (ons_periodicArcStates N imin imax) := by
  exact (ons_allPeriodStates_isChain d N).drop imin.val |>.take _

@[simp] theorem ons_periodicArcStates_head? {n : ℕ} [NeZero n]
    (N : ℕ) (hN : 1 ≤ N) (imin imax : Fin n) :
    (ons_periodicArcStates N imin imax).head? = some (0, imin) := by
  have hcount : N * n + imax.val + 1 - imin.val ≠ 0 := by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hmul : n ≤ N * n := by
      exact Nat.le_mul_of_pos_left n (by omega)
    omega
  rw [ons_periodicArcStates, List.head?_take, if_neg hcount,
    List.head?_drop, ons_allPeriodStates, List.range_succ_eq_map]
  simp only [List.flatMap_cons, ons_periodStateList_length]
  rw [List.getElem?_append_left (by simpa using imin.isLt)]
  rw [ons_periodStateList, List.getElem?_ofFn, dif_pos imin.isLt]

@[simp] theorem ons_periodicArcStates_getLast? {n : ℕ} [NeZero n]
    (N : ℕ) (hN : 1 ≤ N) (imin imax : Fin n) :
    (ons_periodicArcStates N imin imax).getLast? =
      some (N, imax) := by
  let count := N * n + imax.val + 1 - imin.val
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmul : n ≤ N * n := Nat.le_mul_of_pos_left n (by omega)
  have hcount : count ≠ 0 := by
    dsimp [count]
    omega
  rw [ons_periodicArcStates, List.getLast?_take, if_neg hcount,
    List.getElem?_drop]
  have hidx : imin.val + (count - 1) = N * n + imax.val := by
    dsimp [count]
    omega
  rw [hidx, ons_allPeriodStates, List.range_succ,
    List.flatMap_append]
  simp only [List.flatMap_singleton]
  rw [List.getElem?_append_right (by
    simp [List.length_flatMap])]
  simp [ons_periodStateList, List.getElem?_ofFn, imax.isLt]

end StatMech.Onsager
