/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexSweep_runningHead_eq_of_monotone_up (h0 : ℤ) (ts : List ℤ) (i j : ℕ) (hij : i ≤ j)
    (hmono : ∀ k, i ≤ k → k < j → ts[k]?.getD 0 = 1)
    (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6) :
    j = i + 6 := by
  
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  have key : ∀ e, e ≤ d →
      hexStripWinding_runningHead h0 ts (i + e) = hexStripWinding_runningHead h0 ts i + e := by
    intro e he
    induction e with
    | zero => simp
    | succ n ih =>
      have hn : n ≤ d := by omega
      have hlt : n < d := by omega
      have hidx : i + n < ts.length := by
        by_contra hge
        rw [not_lt] at hge
        have : ts[i + n]?.getD 0 = 1 := hmono (i + n) (by omega) (by omega)
        rw [List.getElem?_eq_none (by omega)] at this
        simp at this
      have hstep := hexStripWinding_runningHead_succ h0 ts (i + n) hidx
      have hval : ts[i + n] = 1 := by
        have := hmono (i + n) (by omega) (by omega)
        rwa [List.getElem?_eq_getElem hidx, Option.getD_some] at this
      rw [show i + (n + 1) = (i + n) + 1 from by ring, hstep, ih hn, hval]
      push_cast; ring
  have := key d (le_refl d)
  rw [hsweep] at this
  have hd : (d : ℤ) = 6 := by omega
  omega


theorem hexSweep_runningHead_eq_of_monotone_down (h0 : ℤ) (ts : List ℤ) (i j : ℕ) (hij : i ≤ j)
    (hmono : ∀ k, i ≤ k → k < j → ts[k]?.getD 0 = -1)
    (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i - 6) :
    j = i + 6 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  have key : ∀ e, e ≤ d →
      hexStripWinding_runningHead h0 ts (i + e) = hexStripWinding_runningHead h0 ts i - e := by
    intro e he
    induction e with
    | zero => simp
    | succ n ih =>
      have hn : n ≤ d := by omega
      have hlt : n < d := by omega
      have hidx : i + n < ts.length := by
        by_contra hge
        rw [not_lt] at hge
        have : ts[i + n]?.getD 0 = -1 := hmono (i + n) (by omega) (by omega)
        rw [List.getElem?_eq_none (by omega)] at this
        simp at this
      have hstep := hexStripWinding_runningHead_succ h0 ts (i + n) hidx
      have hval : ts[i + n] = -1 := by
        have := hmono (i + n) (by omega) (by omega)
        rwa [List.getElem?_eq_getElem hidx, Option.getD_some] at this
      rw [show i + (n + 1) = (i + n) + 1 from by ring, hstep, ih hn, hval]
      push_cast; ring
  have := key d (le_refl d)
  rw [hsweep] at this
  have hd : (d : ℤ) = 6 := by omega
  omega


theorem hexSweep_segment_eq_six_left (ts : List ℤ) (i : ℕ) (hlen : i + 6 ≤ ts.length)
    (hmono : ∀ k, i ≤ k → k < i + 6 → ts[k]?.getD 0 = 1) :
    (ts.drop i).take 6 = [(1 : ℤ), 1, 1, 1, 1, 1] := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop]; simp; omega
  · intro n h1 h2
    have hn6 : n < 6 := by
      rw [List.length_take, List.length_drop] at h1; omega
    rw [List.getElem_take, List.getElem_drop]
    have hval := hmono (i + n) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hval
    rw [hval]
    interval_cases n <;> rfl


theorem hexSweep_segment_eq_six_right (ts : List ℤ) (i : ℕ) (hlen : i + 6 ≤ ts.length)
    (hmono : ∀ k, i ≤ k → k < i + 6 → ts[k]?.getD 0 = -1) :
    (ts.drop i).take 6 = [(-1 : ℤ), -1, -1, -1, -1, -1] := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop]; simp; omega
  · intro n h1 h2
    have hn6 : n < 6 := by
      rw [List.length_take, List.length_drop] at h1; omega
    rw [List.getElem_take, List.getElem_drop]
    have hval := hmono (i + n) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hval
    rw [hval]
    interval_cases n <;> rfl


theorem hexSweep_vertexPos_eq_of_six_left (a : ℂ) (h0 : ℤ) (ts : List ℤ) (i : ℕ)
    (hlen : i + 6 ≤ ts.length)
    (hmono : ∀ k, i ≤ k → k < i + 6 → ts[k]?.getD 0 = 1) :
    hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts (i + 6) := by
  have hsplit : ts.take (i + 6) = ts.take i ++ [(1 : ℤ), 1, 1, 1, 1, 1] := by
    rw [List.take_add, hexSweep_segment_eq_six_left ts i hlen hmono]
  unfold hexJordan_vertexPos
  rw [hsplit, hexJordan_midAccum_append, hexJordan_headAccum_append,
    hexJordan_midAccum_six_left]
  have hh : hexInfra_headAccum (hexInfra_headAccum h0 (ts.take i)) [(1 : ℤ), 1, 1, 1, 1, 1]
      = hexInfra_headAccum h0 (ts.take i) + 6 := by
    simp only [hexInfra_headAccum_cons, hexInfra_headAccum_nil]; ring
  rw [hh, hexStrip_halfStep_add6]


theorem hexSweep_vertexPos_eq_of_six_right (a : ℂ) (h0 : ℤ) (ts : List ℤ) (i : ℕ)
    (hlen : i + 6 ≤ ts.length)
    (hmono : ∀ k, i ≤ k → k < i + 6 → ts[k]?.getD 0 = -1) :
    hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts (i + 6) := by
  have hsplit : ts.take (i + 6) = ts.take i ++ [(-1 : ℤ), -1, -1, -1, -1, -1] := by
    rw [List.take_add, hexSweep_segment_eq_six_right ts i hlen hmono]
  unfold hexJordan_vertexPos
  rw [hsplit, hexJordan_midAccum_append, hexJordan_headAccum_append,
    hexJordan_midAccum_six_right]
  have hh : hexInfra_headAccum (hexInfra_headAccum h0 (ts.take i)) [(-1 : ℤ), -1, -1, -1, -1, -1]
      = hexInfra_headAccum h0 (ts.take i) - 6 := by
    simp only [hexInfra_headAccum_cons, hexInfra_headAccum_nil]; ring
  rw [hh]
  have h6 := hexStrip_halfStep_add6 (hexInfra_headAccum h0 (ts.take i) - 6)
  rw [show (hexInfra_headAccum h0 (ts.take i) - 6 + 6 : ℤ) = hexInfra_headAccum h0 (ts.take i)
    from by ring] at h6
  rw [h6]


theorem hexSweep_vertexPos_eq_of_monotone_up (a : ℂ) (h0 : ℤ) (ts : List ℤ) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ ts.length)
    (hmono : ∀ k, i ≤ k → k < j → ts[k]?.getD 0 = 1)
    (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6) :
    hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j := by
  have hj6 : j = i + 6 := hexSweep_runningHead_eq_of_monotone_up h0 ts i j hij hmono hsweep
  subst hj6
  exact hexSweep_vertexPos_eq_of_six_left a h0 ts i hj
    (fun k hk hk' => hmono k hk hk')


theorem hexSweep_vertexPos_eq_of_monotone_down (a : ℂ) (h0 : ℤ) (ts : List ℤ) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ ts.length)
    (hmono : ∀ k, i ≤ k → k < j → ts[k]?.getD 0 = -1)
    (hsweep : hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i - 6) :
    hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j := by
  have hj6 : j = i + 6 := hexSweep_runningHead_eq_of_monotone_down h0 ts i j hij hmono hsweep
  subst hj6
  exact hexSweep_vertexPos_eq_of_six_right a h0 ts i hj
    (fun k hk hk' => hmono k hk hk')


end StatMech.Universality
