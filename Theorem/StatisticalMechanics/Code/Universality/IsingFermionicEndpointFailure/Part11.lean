/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part14


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem lineFreeEndpoint_eq_start_add_sum_endpointFailure
    (start : Int) (bs : List Bool) :
    lineFreeEndpoint start bs =
      start + (bs.map endpointFailureLineStep).sum := by
  induction bs generalizing start with
  | nil => simp [lineFreeEndpoint]
  | cons b bs ih =>
      rw [lineFreeEndpoint, ih]
      simp [endpointFailureLineStep]
      ring

theorem endpointFailureLineStep_not (b : Bool) :
    endpointFailureLineStep (!b) = -endpointFailureLineStep b := by
  cases b <;> simp [endpointFailureLineStep]

theorem sum_map_lineStep_not_endpointFailure (bs : List Bool) :
    ((bs.map (!.)).map endpointFailureLineStep).sum =
      -(bs.map endpointFailureLineStep).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      simp only [List.map_cons, List.sum_cons, endpointFailureLineStep_not]
      rw [ih]
      ring

theorem sum_map_lineStep_reverse_endpointFailure (bs : List Bool) :
    (bs.reverse.map endpointFailureLineStep).sum =
      (bs.map endpointFailureLineStep).sum := by
  rw [List.map_reverse, List.sum_reverse]

theorem sum_map_lineStep_reverse_not_endpointFailure (bs : List Bool) :
    ((bs.reverse.map (!.)).map endpointFailureLineStep).sum =
      -(bs.map endpointFailureLineStep).sum := by
  rw [sum_map_lineStep_not_endpointFailure,
    sum_map_lineStep_reverse_endpointFailure]

theorem lineFirstEndpoint_free_prefix
    (n k : Nat) (start target : IsingLineBox n)
    (w : IsingLineFirstEndpointFamily n k start target) :
    forall l, l <= k ->
      ((isingLineChoiceRun n start (w.1.take l)).1 : Int) =
        lineFreeEndpoint (start.1 : Int) (w.1.take l) := by
  intro l hl
  induction l using Nat.strong_induction_on with
  | h l ih =>
      apply lineChoiceRun_val_eq_lineFreeEndpoint
      intro r hr
      have hrl : r < l := by
        rw [List.length_take, w.2.1] at hr
        omega
      have hrk : r < k := lt_of_lt_of_le hrl hl
      have hrunInterior := w.2.2.2 r hrk
      have hrunFree := ih r hrl (by omega)
      have htake : (w.1.take l).take r = w.1.take r := by
        simp [List.take_take, Nat.min_eq_left hrl.le]
      rw [htake]
      constructor
      · intro hzero
        apply hrunInterior
        unfold isingLineBoxBoundary
        left
        have hcast :
            ((isingLineChoiceRun n start (w.1.take r)).1 : Int) = 0 := by
          rw [hrunFree, hzero]
        exact_mod_cast hcast
      · intro hn
        apply hrunInterior
        unfold isingLineBoxBoundary
        right
        have hcast :
            ((isingLineChoiceRun n start (w.1.take r)).1 : Int) = n := by
          rw [hrunFree, hn]
        exact_mod_cast hcast

theorem lineFirstEndpoint_time_pos
    (n k : Nat) (start target : IsingLineBox n)
    (hstart : ¬ isingLineBoxBoundary n start)
    (htarget : isingLineBoxBoundary n target)
    (w : IsingLineFirstEndpointFamily n k start target) :
    0 < k := by
  by_contra hk
  have hk0 : k = 0 := by omega
  have hout := w.2.2.1
  subst k
  have hwNil : w.1 = [] := List.eq_nil_of_length_eq_zero w.2.1
  rw [hwNil] at hout
  simp [isingLineChoiceRun] at hout
  subst target
  exact hstart htarget

theorem lineFirstEndpoint_dropLast_data
    (n k : Nat) (start target : IsingLineBox n)
    (w : IsingLineFirstEndpointFamily n k start target)
    (hk : 0 < k) :
    let pref := w.1.dropLast
    pref.length = k - 1 /\
      lineFreeEndpoint (start.1 : Int) pref =
        ((isingLineChoiceRun n start pref).1 : Int) /\
      (forall l, l <= pref.length ->
        lineFreeEndpoint (start.1 : Int) (pref.take l) ≠ 0 /\
        lineFreeEndpoint (start.1 : Int) (pref.take l) ≠ n) := by
  let pref := w.1.dropLast
  have hprefLen : pref.length = k - 1 := by
    dsimp [pref]
    rw [List.length_dropLast, w.2.1]
  have hprefTake : w.1.take (k - 1) = pref := by
    dsimp [pref]
    rw [List.dropLast_eq_take, w.2.1]
  have hfree := lineFirstEndpoint_free_prefix n k start target w (k - 1) (by omega)
  rw [hprefTake] at hfree
  refine ⟨hprefLen, hfree.symm, ?_⟩
  intro l hl
  change l <= pref.length at hl
  have hlk : l < k := by omega
  have hrunInterior := w.2.2.2 l hlk
  have htake : pref.take l = w.1.take l := by
    rw [← hprefTake, List.take_take]
    simp [Nat.min_eq_left (by omega : l <= k - 1)]
  have hrunFree := lineFirstEndpoint_free_prefix n k start target w l hlk.le
  rw [← htake] at hrunFree
  constructor
  · intro hzero
    apply hrunInterior
    unfold isingLineBoxBoundary
    left
    change lineFreeEndpoint (start.1 : Int) (pref.take l) = 0 at hzero
    have : ((isingLineChoiceRun n start (w.1.take l)).1 : Int) = 0 := by
      rw [← htake, hrunFree, hzero]
    exact_mod_cast this
  · intro hn
    apply hrunInterior
    unfold isingLineBoxBoundary
    right
    change lineFreeEndpoint (start.1 : Int) (pref.take l) = n at hn
    have : ((isingLineChoiceRun n start (w.1.take l)).1 : Int) = n := by
      rw [← htake, hrunFree, hn]
    exact_mod_cast this

theorem lineFirstEndpoint_left_dropLast
    (n k : Nat) (start target : IsingLineBox n)
    (w : IsingLineFirstEndpointFamily n k start target)
    (hk : 0 < k) (htarget : target.1 = 0) :
    lineFreeEndpoint (start.1 : Int) w.1.dropLast = 1 /\
      w.1 = w.1.dropLast ++ [false] := by
  let pref := w.1.dropLast
  have hwNe : w.1 ≠ [] := by
    intro hw
    have hlen := w.2.1
    rw [hw] at hlen
    simp at hlen
    omega
  have hdecomp := List.dropLast_append_getLast hwNe
  have hdata := lineFirstEndpoint_dropLast_data n k start target w hk
  dsimp only at hdata
  have hprefFree := hdata.2.1
  have hprefNonneg : 0 <= lineFreeEndpoint (start.1 : Int) pref := by
    rw [hprefFree]
    positivity
  have hfullFree := lineFirstEndpoint_free_prefix n k start target w k le_rfl
  have htake : w.1.take k = w.1 := by
    simpa [w.2.1] using List.take_all w.1
  rw [htake, w.2.2.1] at hfullFree
  have hfullZero : lineFreeEndpoint (start.1 : Int) w.1 = 0 := by
    rw [← hfullFree]
    exact_mod_cast htarget
  rw [← hdecomp,
    lineFreeEndpoint_append_endpointFailure] at hfullZero
  change lineFreeEndpoint (lineFreeEndpoint (start.1 : Int) pref)
    [w.1.getLast hwNe] = 0 at hfullZero
  have hlast : w.1.getLast hwNe = false := by
    cases h : w.1.getLast hwNe
    · rfl
    · simp [lineFreeEndpoint, h] at hfullZero
      omega
  constructor
  · rw [hlast] at hfullZero
    change lineFreeEndpoint (start.1 : Int) pref - 1 = 0 at hfullZero
    change lineFreeEndpoint (start.1 : Int) pref = 1
    omega
  · simpa [pref, hlast] using hdecomp.symm

theorem lineFirstEndpoint_right_dropLast
    (n k : Nat) (start target : IsingLineBox n)
    (w : IsingLineFirstEndpointFamily n k start target)
    (hk : 0 < k) (htarget : target.1 = n) :
    lineFreeEndpoint (start.1 : Int) w.1.dropLast = (n : Int) - 1 /\
      w.1 = w.1.dropLast ++ [true] := by
  let pref := w.1.dropLast
  have hwNe : w.1 ≠ [] := by
    intro hw
    have hlen := w.2.1
    rw [hw] at hlen
    simp at hlen
    omega
  have hdecomp := List.dropLast_append_getLast hwNe
  have hdata := lineFirstEndpoint_dropLast_data n k start target w hk
  dsimp only at hdata
  have hprefFree := hdata.2.1
  have hprefLe : lineFreeEndpoint (start.1 : Int) pref <= n := by
    rw [hprefFree]
    exact_mod_cast Nat.lt_succ_iff.mp (isingLineChoiceRun n start pref).2
  have hfullFree := lineFirstEndpoint_free_prefix n k start target w k le_rfl
  have htake : w.1.take k = w.1 := by
    simpa [w.2.1] using List.take_all w.1
  rw [htake, w.2.2.1] at hfullFree
  have hfullRight : lineFreeEndpoint (start.1 : Int) w.1 = n := by
    rw [← hfullFree]
    exact_mod_cast htarget
  rw [← hdecomp,
    lineFreeEndpoint_append_endpointFailure] at hfullRight
  change lineFreeEndpoint (lineFreeEndpoint (start.1 : Int) pref)
    [w.1.getLast hwNe] = n at hfullRight
  have hlast : w.1.getLast hwNe = true := by
    cases h : w.1.getLast hwNe
    · simp [lineFreeEndpoint, h] at hfullRight
      omega
    · rfl
  constructor
  · rw [hlast] at hfullRight
    change lineFreeEndpoint (start.1 : Int) pref + 1 = n at hfullRight
    change lineFreeEndpoint (start.1 : Int) pref = (n : Int) - 1
    omega
  · simpa [pref, hlast] using hdecomp.symm

end
end StatMech.Universality
