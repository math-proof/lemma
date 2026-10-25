/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Def.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part8


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

theorem ons_allPeriodStates_map_direction {n : ℕ}
    (d : Fin n → Fin 4) (N : ℕ) :
    (ons_allPeriodStates n N).map (fun z ↦ d z.2) =
      ons_directionPeriods d (N + 1) := by
  simp [ons_allPeriodStates, ons_periodStateList,
    ons_directionPeriods, List.map_flatMap, List.map_ofFn]
  apply List.flatMap_congr
  intro r hr
  congr 1

theorem ons_dropLast_take_of_pos_le {X : Type*}
    (l : List X) (k : ℕ) (hk : 0 < k) (hle : k ≤ l.length) :
    (l.take k).dropLast = l.take (k - 1) := by
  rw [List.dropLast_eq_take, List.length_take, Nat.min_eq_left hle,
    List.take_take]
  rw [Nat.min_eq_left]
  omega

theorem ons_periodicArcDirections_eq_slice {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    ons_periodicArcDirections d N imin imax =
      ((ons_directionPeriods d (N + 1)).drop imin.val).take
        (N * n + imax.val - imin.val) := by
  let count := N * n + imax.val + 1 - imin.val
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmul : n ≤ N * n := Nat.le_mul_of_pos_left n (by omega)
  have hcount : 0 < count := by
    dsimp [count]
    omega
  have hle : count ≤
      ((ons_directionPeriods d (N + 1)).drop imin.val).length := by
    rw [List.length_drop]
    simp [ons_directionPeriods, List.length_flatMap]
    rw [Nat.add_mul]
    dsimp [count]
    omega
  rw [ons_periodicArcDirections, ons_periodicArcStates,
    List.map_dropLast, List.map_take, List.map_drop,
    ons_allPeriodStates_map_direction,
    ons_dropLast_take_of_pos_le _ count hcount hle]
  congr 1
  dsimp [count]
  omega

@[simp] theorem ons_directionPeriods_length {n : ℕ}
    (d : Fin n → Fin 4) (N : ℕ) :
    (ons_directionPeriods d N).length = N * n := by
  simp [ons_directionPeriods, List.length_flatMap]

theorem ons_directionPeriods_succ {n : ℕ}
    (d : Fin n → Fin 4) (N : ℕ) :
    ons_directionPeriods d (N + 1) =
      ons_directionPeriods d N ++ List.ofFn d := by
  simp [ons_directionPeriods, List.range_succ, List.flatMap_append]

theorem ons_directionPeriods_append_comm {n : ℕ}
    (d : Fin n → Fin 4) (N : ℕ) :
    ons_directionPeriods d N ++ List.ofFn d =
      List.ofFn d ++ ons_directionPeriods d N := by
  induction N with
  | zero => simp [ons_directionPeriods]
  | succ N ih =>
      rw [show N + 1 = N + 1 by rfl, ons_directionPeriods_succ]
      rw [← List.append_assoc, ih, List.append_assoc]

theorem ons_directionPeriods_succ_left {n : ℕ}
    (d : Fin n → Fin 4) (N : ℕ) :
    ons_directionPeriods d (N + 1) =
      List.ofFn d ++ ons_directionPeriods d N := by
  rw [ons_directionPeriods_succ,
    ons_directionPeriods_append_comm]

theorem ons_periodicArcDirections_eq_blocks {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    ons_periodicArcDirections d N imin imax =
      (List.ofFn d).drop imin.val ++
        ons_directionPeriods d (N - 1) ++
        (List.ofFn d).take imax.val := by
  rw [ons_periodicArcDirections_eq_slice d N hN,
    ons_directionPeriods_succ_left]
  rw [List.drop_append, List.take_append]
  simp only [List.length_ofFn]
  have hdrop : imin.val - n = 0 := by omega
  rw [hdrop, List.drop_zero]
  have hfirst :
      ((List.ofFn d).drop imin.val).take
          (N * n + imax.val - imin.val) =
        (List.ofFn d).drop imin.val := by
    apply (List.take_eq_self_iff _).mpr
    rw [List.length_drop, List.length_ofFn]
    have hmul : n ≤ N * n := Nat.le_mul_of_pos_left n (by omega)
    omega
  rw [hfirst]
  rw [List.length_drop, List.length_ofFn]
  have hNsplit : N = (N - 1) + 1 := by omega
  have hmulEq : N * n = (N - 1) * n + n := by
    rw [hNsplit, Nat.add_mul]
    simp
  have hrem : N * n + imax.val - imin.val - (n - imin.val) =
      (N - 1) * n + imax.val := by
    rw [hmulEq]
    omega
  rw [hrem]
  conv_lhs =>
    rhs
    rw [hNsplit, ons_directionPeriods_succ]
  rw [List.take_append]
  simp only [ons_directionPeriods_length]
  have htakePeriods :
      (ons_directionPeriods d (N - 1)).take
          ((N - 1) * n + imax.val) =
        ons_directionPeriods d (N - 1) := by
    apply (List.take_eq_self_iff _).mpr
    simp
  have hnorm : N - 1 + 1 - 1 = N - 1 := by omega
  rw [hnorm]
  rw [htakePeriods]
  rw [Nat.add_sub_cancel_left]
  exact (List.append_assoc _ _ _).symm

theorem ons_getLast!_append_of_right_ne_nil {X : Type*} [Inhabited X]
    (l r : List X) (hr : r ≠ []) :
    (l ++ r).getLast! = r.getLast! := by
  have hlr : l ++ r ≠ [] := List.append_ne_nil_of_right_ne_nil l hr
  rw [ons_getLast!_eq_getLast (l ++ r) hlr,
    ons_getLast!_eq_getLast r hr]
  rw [List.getLast_append]
  simp [hr]

theorem ons_openTurnSum_insert_cycle
    (A D P : List (Fin 4)) (hA : A ≠ []) (hD : D ≠ [])
    (hlast : A.getLast! = D.getLast!)
    (hhead : P ≠ [] → P.head! = D.head!) :
    ons_openTurnSum (A ++ D ++ P) =
      ons_openTurnSum (A ++ P) + ons_cyclicTurnSum D := by
  have hAD : A ++ D ≠ [] := List.append_ne_nil_of_right_ne_nil A hD
  have hcyc : ons_cyclicTurnSum D =
      ons_openTurnSum D + ons_turnPow D.getLast! D.head! := by
    obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hD
    rfl
  by_cases hP : P = []
  · subst P
    simp only [List.append_nil]
    rw [ons_openTurnSum_append A D hA hD, hcyc, hlast]
    abel
  · rw [ons_openTurnSum_append (A ++ D) P hAD hP,
      ons_openTurnSum_append A D hA hD,
      ons_openTurnSum_append A P hA hP,
      ons_getLast!_append_of_right_ne_nil A D hD,
      hhead hP, hcyc, hlast]
    abel

theorem ons_adjustedTurn_insert_cycle
    (A D P : List (Fin 4)) (hA : A ≠ []) (hD : D ≠ [])
    (hlast : A.getLast! = D.getLast!)
    (hhead : P ≠ [] → P.head! = D.head!) :
    let old := A ++ P
    let new := A ++ D ++ P
    ons_openTurnSum new + ons_turnPow new.getLast! 0 + 4 +
        ons_turnPow 0 new.head! =
      ons_openTurnSum old + ons_turnPow old.getLast! 0 + 4 +
        ons_turnPow 0 old.head! + ons_cyclicTurnSum D := by
  dsimp
  rw [ons_openTurnSum_insert_cycle A D P hA hD hlast hhead]
  have hheadOld : (A ++ P).head! = A.head! := by simp [hA]
  have hheadNew : (A ++ D ++ P).head! = A.head! := by simp [hA]
  rw [hheadOld, hheadNew]
  by_cases hP : P = []
  · subst P
    simp only [List.append_nil]
    rw [ons_getLast!_append_of_right_ne_nil A D hD, hlast]
    abel
  · rw [ons_getLast!_append_of_right_ne_nil A P hP,
      ons_getLast!_append_of_right_ne_nil (A ++ D) P hP]
    abel

theorem ons_ofFn_ne_nil {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) : List.ofFn d ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this
  exact NeZero.ne n this

theorem ons_drop_ofFn_ne_nil {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (i : Fin n) :
    (List.ofFn d).drop i.val ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [List.length_drop, List.length_ofFn] at this
  simp at this
  omega

theorem ons_drop_ofFn_getLast! {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (i : Fin n) :
    ((List.ofFn d).drop i.val).getLast! = (List.ofFn d).getLast! := by
  have hdrop := ons_drop_ofFn_ne_nil d i
  have hsplit := List.take_append_drop i.val (List.ofFn d)
  calc
    ((List.ofFn d).drop i.val).getLast! =
        ((List.ofFn d).take i.val ++
          (List.ofFn d).drop i.val).getLast! :=
      (ons_getLast!_append_of_right_ne_nil
        ((List.ofFn d).take i.val) ((List.ofFn d).drop i.val) hdrop).symm
    _ = (List.ofFn d).getLast! := congrArg List.getLast! hsplit

theorem ons_directionPeriods_getLast! {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N) :
    (ons_directionPeriods d N).getLast! = (List.ofFn d).getLast! := by
  have hsplit : N = (N - 1) + 1 := by omega
  rw [hsplit, ons_directionPeriods_succ]
  exact ons_getLast!_append_of_right_ne_nil
    (ons_directionPeriods d (N - 1)) (List.ofFn d)
    (ons_ofFn_ne_nil d)

theorem ons_arcInitialBlock_getLast! {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin : Fin n) :
    ((List.ofFn d).drop imin.val ++
      ons_directionPeriods d (N - 1)).getLast! =
        (List.ofFn d).getLast! := by
  by_cases hzero : N - 1 = 0
  · rw [hzero]
    change (((List.ofFn d).drop imin.val) ++ []).getLast! = _
    rw [List.append_nil]
    exact ons_drop_ofFn_getLast! d imin
  · have hpos : 1 ≤ N - 1 := Nat.one_le_iff_ne_zero.mpr hzero
    have hperiods : ons_directionPeriods d (N - 1) ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      rw [ons_directionPeriods_length] at hlen
      simp at hlen
      rcases hlen with hleft | hright
      · exact hzero hleft
      · exact NeZero.ne n hright
    rw [ons_getLast!_append_of_right_ne_nil
      ((List.ofFn d).drop imin.val)
      (ons_directionPeriods d (N - 1)) hperiods]
    exact ons_directionPeriods_getLast! d (N - 1) hpos

theorem ons_head!_eq_head {X : Type*} [Inhabited X]
    (l : List X) (h : l ≠ []) :
    l.head! = l.head h := by
  cases l with
  | nil => exact (h rfl).elim
  | cons a as => rfl

theorem ons_take_ofFn_head! {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (i : Fin n)
    (h : (List.ofFn d).take i.val ≠ []) :
    ((List.ofFn d).take i.val).head! = (List.ofFn d).head! := by
  have hfull := ons_ofFn_ne_nil d
  rw [ons_head!_eq_head ((List.ofFn d).take i.val) h,
    ons_head!_eq_head (List.ofFn d) hfull]
  exact List.head_take h

theorem ons_periodicArc_adjustedTurn_succ {n : ℕ} [NeZero n]
    (d : Fin n → Fin 4) (N : ℕ) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    let old := ons_periodicArcDirections d N imin imax
    let new := ons_periodicArcDirections d (N + 1) imin imax
    ons_openTurnSum new + ons_turnPow new.getLast! 0 + 4 +
        ons_turnPow 0 new.head! =
      ons_openTurnSum old + ons_turnPow old.getLast! 0 + 4 +
        ons_turnPow 0 old.head! +
          ons_cyclicTurnSum (List.ofFn d) := by
  let S := (List.ofFn d).drop imin.val
  let M := ons_directionPeriods d (N - 1)
  let D := List.ofFn d
  let P := (List.ofFn d).take imax.val
  let A := S ++ M
  have hA : A ≠ [] := by
    exact List.append_ne_nil_of_left_ne_nil
      (ons_drop_ofFn_ne_nil d imin) M
  have hD : D ≠ [] := ons_ofFn_ne_nil d
  have hlast : A.getLast! = D.getLast! := by
    exact ons_arcInitialBlock_getLast! d N hN imin
  have hhead : P ≠ [] → P.head! = D.head! := by
    intro hP
    exact ons_take_ofFn_head! d imax hP
  have hinsert := ons_adjustedTurn_insert_cycle A D P hA hD hlast hhead
  dsimp only
  rw [ons_periodicArcDirections_eq_blocks d N hN,
    ons_periodicArcDirections_eq_blocks d (N + 1) (by omega)]
  have hsplit : N = (N - 1) + 1 := by omega
  have hper : ons_directionPeriods d N =
      ons_directionPeriods d (N - 1) ++ List.ofFn d := by
    conv_lhs => rw [hsplit]
    exact ons_directionPeriods_succ d (N - 1)
  have hsuccsub : N + 1 - 1 = N := by omega
  rw [hsuccsub, hper]
  simpa only [S, M, D, P, A, List.append_assoc] using hinsert

theorem ons_periodicSimple_cyclicTurnSum_eq_zero
    {n : ℕ} [NeZero n] (d : Fin n → Fin 4)
    (hinj : Function.Injective (ons_periodStateCoord d))
    (hD : 0 < (ons_pathDisplacement (List.ofFn d)).1) :
    ons_cyclicTurnSum (List.ofFn d) = 0 := by
  obtain ⟨imin, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin n ↦ (pos d i).1) Finset.univ_nonempty
  obtain ⟨imax, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n ↦ (pos d i).1) Finset.univ_nonempty
  have hmin' : ∀ i, (pos d imin).1 ≤ (pos d i).1 := by
    intro i
    exact hmin i (Finset.mem_univ i)
  have hmax' : ∀ i, (pos d i).1 ≤ (pos d imax).1 := by
    intro i
    exact hmax i (Finset.mem_univ i)
  let adj (N : ℕ) : ℤ :=
    let l := ons_periodicArcDirections d N imin imax
    ons_openTurnSum l + ons_turnPow l.getLast! 0 + 4 +
      ons_turnPow 0 l.head!
  have h1 : adj 1 = 4 ∨ adj 1 = -4 := by
    simpa [adj] using ons_periodicArc_adjustedTurn_eq_four_or_neg_four
      d 1 (by omega) imin imax hinj hmin' hmax' hD
  have h2 : adj 2 = 4 ∨ adj 2 = -4 := by
    simpa [adj] using ons_periodicArc_adjustedTurn_eq_four_or_neg_four
      d 2 (by omega) imin imax hinj hmin' hmax' hD
  have h3 : adj 3 = 4 ∨ adj 3 = -4 := by
    simpa [adj] using ons_periodicArc_adjustedTurn_eq_four_or_neg_four
      d 3 (by omega) imin imax hinj hmin' hmax' hD
  have h12 : adj 2 = adj 1 + ons_cyclicTurnSum (List.ofFn d) := by
    simpa [adj] using ons_periodicArc_adjustedTurn_succ
      d 1 (by omega) imin imax
  have h23 : adj 3 = adj 2 + ons_cyclicTurnSum (List.ofFn d) := by
    simpa [adj] using ons_periodicArc_adjustedTurn_succ
      d 2 (by omega) imin imax
  rw [h12] at h2
  have h13 : adj 3 = adj 1 +
      2 * ons_cyclicTurnSum (List.ofFn d) := by
    rw [h23, h12]
    ring
  rw [h13] at h3
  exact ons_three_values_force_step_zero
    (adj 1) (ons_cyclicTurnSum (List.ofFn d)) h1 h2 h3

end StatMech.Onsager
