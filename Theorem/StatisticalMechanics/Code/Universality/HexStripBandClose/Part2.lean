/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripWindingClose.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Def.StatisticalMechanics.Code.Universality.HexStripBandClose


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexJordan_vertexPos_ne_of_saw (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).IsSAW) (i j : ℕ) (hi : i ≤ ts.length) (hj : j ≤ ts.length)
    (hne : i ≠ j) :
    hexJordan_vertexPos a h0 ts i ≠ hexJordan_vertexPos a h0 ts j := by
  intro heq
  unfold HexWalk.IsSAW HexWalk.vertices at hsaw
  simp only [ofTurns] at hsaw
  have hilen : i < (verticesAux a h0 ts).length := by rw [length_verticesAux]; omega
  have hjlen : j < (verticesAux a h0 ts).length := by rw [length_verticesAux]; omega
  have hvi := hexJordan_verticesAux_getElem?_eq a h0 ts i hi
  have hvj := hexJordan_verticesAux_getElem?_eq a h0 ts j hj
  have he2 : (verticesAux a h0 ts)[i]? = (verticesAux a h0 ts)[j]? := by
    rw [hvi, hvj]; unfold hexJordan_vertexPos at heq; rw [heq]
  rw [List.getElem?_eq_getElem hilen, List.getElem?_eq_getElem hjlen, Option.some.injEq] at he2
  exact hne ((List.getElem_inj hsaw).mp he2)


theorem hexJordan_sum_hexUnit_six (h : ℤ) :
    hexUnit h + hexUnit (h + 1) + hexUnit (h + 2)
      + hexUnit (h + 3) + hexUnit (h + 4) + hexUnit (h + 5) = 0 := by
  have h3 : hexUnit (h + 3) = - hexUnit h := hexUnit_add_three h
  have h4 : hexUnit (h + 4) = - hexUnit (h + 1) := by
    rw [show (h + 4 : ℤ) = (h + 1) + 3 from by ring, hexUnit_add_three]
  have h5 : hexUnit (h + 5) = - hexUnit (h + 2) := by
    rw [show (h + 5 : ℤ) = (h + 2) + 3 from by ring, hexUnit_add_three]
  rw [h3, h4, h5]; ring


theorem hexJordan_midAccum_six_left (a : ℂ) (h0 : ℤ) :
    hexInfra_midAccum a h0 [(1 : ℤ), 1, 1, 1, 1, 1] = a := by
  simp only [hexInfra_midAccum_cons, hexInfra_midAccum_nil]
  unfold HexWalk.halfStep
  have R : ∀ h : ℤ, hexUnit (h + 3) = - hexUnit h := hexUnit_add_three
  have a3 : hexUnit (h0 + 1 + 1 + 1) = - hexUnit h0 := by
    rw [show (h0 + 1 + 1 + 1 : ℤ) = h0 + 3 from by ring, R]
  have a4 : hexUnit (h0 + 1 + 1 + 1 + 1) = - hexUnit (h0 + 1) := by
    rw [show (h0 + 1 + 1 + 1 + 1 : ℤ) = (h0 + 1) + 3 from by ring, R]
  have a5 : hexUnit (h0 + 1 + 1 + 1 + 1 + 1) = - hexUnit (h0 + 1 + 1) := by
    rw [show (h0 + 1 + 1 + 1 + 1 + 1 : ℤ) = (h0 + 1 + 1) + 3 from by ring, R]
  have a6 : hexUnit (h0 + 1 + 1 + 1 + 1 + 1 + 1) = hexUnit h0 := by
    rw [show (h0 + 1 + 1 + 1 + 1 + 1 + 1 : ℤ) = h0 + 6 from by ring, hexUnit_add_six]
  rw [a3, a4, a5, a6]; ring


theorem hexJordan_midAccum_six_right (a : ℂ) (h0 : ℤ) :
    hexInfra_midAccum a h0 [(-1 : ℤ), -1, -1, -1, -1, -1] = a := by
  simp only [hexInfra_midAccum_cons, hexInfra_midAccum_nil]
  unfold HexWalk.halfStep
  have Rm : ∀ h : ℤ, hexUnit (h - 3) = - hexUnit h := by
    intro h
    have := hexUnit_add_three (h - 3)
    rw [show (h - 3 + 3 : ℤ) = h from by ring] at this
    linear_combination this
  have a3 : hexUnit (h0 + -1 + -1 + -1) = - hexUnit h0 := by
    rw [show (h0 + -1 + -1 + -1 : ℤ) = h0 - 3 from by ring, Rm]
  have a4 : hexUnit (h0 + -1 + -1 + -1 + -1) = - hexUnit (h0 + -1) := by
    rw [show (h0 + -1 + -1 + -1 + -1 : ℤ) = (h0 + -1) - 3 from by ring, Rm]
  have a5 : hexUnit (h0 + -1 + -1 + -1 + -1 + -1) = - hexUnit (h0 + -1 + -1) := by
    rw [show (h0 + -1 + -1 + -1 + -1 + -1 : ℤ) = (h0 + -1 + -1) - 3 from by ring, Rm]
  have a6 : hexUnit (h0 + -1 + -1 + -1 + -1 + -1 + -1) = hexUnit h0 := by
    rw [show (h0 + -1 + -1 + -1 + -1 + -1 + -1 : ℤ) = h0 - 6 from by ring,
      show (h0 - 6 : ℤ) = (h0 - 3) - 3 from by ring, Rm, Rm]; ring
  rw [a3, a4, a5, a6]; ring


theorem hexJordan_headAccum_append (h : ℤ) (s t : List ℤ) :
    hexInfra_headAccum h (s ++ t) = hexInfra_headAccum (hexInfra_headAccum h s) t := by
  induction s generalizing h with
  | nil => simp
  | cons x s ih => simp only [List.cons_append, hexInfra_headAccum_cons, ih]


theorem hexJordan_midAccum_append (m : ℂ) (h : ℤ) (s t : List ℤ) :
    hexInfra_midAccum m h (s ++ t)
      = hexInfra_midAccum (hexInfra_midAccum m h s) (hexInfra_headAccum h s) t := by
  induction s generalizing m h with
  | nil => simp
  | cons x s ih =>
    simp only [List.cons_append, hexInfra_midAccum_cons, hexInfra_headAccum_cons, ih]


theorem hexJordan_no_revolution_pair (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).IsSAW)
    (hclose : ∀ i j, i ≤ ts.length → j ≤ ts.length →
      hexStripWinding_runningHead h0 ts j = hexStripWinding_runningHead h0 ts i + 6 →
      hexJordan_vertexPos a h0 ts i = hexJordan_vertexPos a h0 ts j) :
    ∀ i j, i ≤ ts.length → j ≤ ts.length →
      hexStripWinding_runningHead h0 ts j ≠ hexStripWinding_runningHead h0 ts i + 6 := by
  intro i j hi hj heq
  have hposeq := hclose i j hi hj heq
  have hne : i ≠ j := by rintro rfl; omega
  exact hexJordan_vertexPos_ne_of_saw a h0 ts hsaw i j hi hj hne hposeq


theorem hexJordan_span_lt_six (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hno6 : ∀ i j, i ≤ ts.length → j ≤ ts.length →
      hexStripWinding_runningHead h0 ts j ≠ hexStripWinding_runningHead h0 ts i + 6) :
    ∀ i j, i ≤ ts.length → j ≤ ts.length →
      |hexStripWinding_runningHead h0 ts i - hexStripWinding_runningHead h0 ts j| < 6 := by
  have keyUp : ∀ i j, i ≤ j → j ≤ ts.length →
      hexStripWinding_runningHead h0 ts j - hexStripWinding_runningHead h0 ts i < 6 := by
    intro i j hij hj
    by_contra hge
    rw [not_lt] at hge
    set f := fun n => hexStripWinding_runningHead h0 ts n with hf
    have hle : f i ≤ f j := by simp only [hf]; omega
    have hm1 : min (f i) (f j) ≤ f i + 6 := by rw [min_eq_left hle]; simp only [hf]; omega
    have hm2 : f i + 6 ≤ max (f i) (f j) := by rw [max_eq_right hle]; simp only [hf]; omega
    obtain ⟨c, hci, hcj, hcm⟩ := hexUmlauf_runningHead_IVT a h0 ts hlegal i j hij hj
      (hexStripWinding_runningHead h0 ts i + 6) hm1 hm2
    exact hno6 i c (by omega) (by omega) hcm
  have keyDown : ∀ i j, i ≤ j → j ≤ ts.length →
      hexStripWinding_runningHead h0 ts i - hexStripWinding_runningHead h0 ts j < 6 := by
    intro i j hij hj
    by_contra hge
    rw [not_lt] at hge
    set f := fun n => hexStripWinding_runningHead h0 ts n with hf
    have hle : f j ≤ f i := by simp only [hf]; omega
    have hm1 : min (f i) (f j) ≤ f j + 6 := by rw [min_eq_right hle]; simp only [hf]; omega
    have hm2 : f j + 6 ≤ max (f i) (f j) := by rw [max_eq_left hle]; simp only [hf]; omega
    obtain ⟨c, hci, hcj, hcm⟩ := hexUmlauf_runningHead_IVT a h0 ts hlegal i j hij hj
      (hexStripWinding_runningHead h0 ts j + 6) hm1 hm2
    exact hno6 j c hj (by omega) hcm
  intro i j hi hj
  rw [abs_lt]
  rcases le_total i j with h | h
  · exact ⟨by have := keyUp i j h hj; omega, by have := keyDown i j h hj; omega⟩
  · exact ⟨by have := keyDown j i h hi; omega, by have := keyUp j i h hi; omega⟩


theorem hexJordan_window_of_span_attained (h0 w : ℤ) (ts : List ℤ)
    (hspan : ∀ i j, i ≤ ts.length → j ≤ ts.length →
      |hexStripWinding_runningHead h0 ts i - hexStripWinding_runningHead h0 ts j| < 6)
    (p : ℕ) (hp : p ≤ ts.length) (hpw : hexStripWinding_runningHead h0 ts p = w)
    (hfloor : ∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k) :
    (∀ k, k ≤ ts.length → w ≤ hexStripWinding_runningHead h0 ts k)
      ∧ (∀ k, k ≤ ts.length → hexStripWinding_runningHead h0 ts k ≠ w + 6) := by
  refine ⟨hfloor, ?_⟩
  intro k hk heq
  have hsp := hspan p k hp hk
  rw [hpw, heq, abs_lt] at hsp
  omega


end StatMech.Universality
