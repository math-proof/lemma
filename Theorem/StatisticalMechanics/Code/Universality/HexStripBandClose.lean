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


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexJordan_runningHead_eq_headAccum_take (h0 : ℤ) (ts : List ℤ) (k : ℕ) :
    hexStripWinding_runningHead h0 ts k = hexInfra_headAccum h0 (ts.take k) := by
  rw [hexInfra_headAccum_eq_add_sum]; rfl


theorem hexJordan_midsAux_getElem?_eq (m : ℂ) (h : ℤ) (ts : List ℤ) (k : ℕ) (hk : k ≤ ts.length) :
    (midsAux m h ts)[k]? = some (hexInfra_midAccum m h (ts.take k)) := by
  induction ts generalizing m h k with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hk
    subst hk
    simp [midsAux]
  | cons t ts ih =>
    cases k with
    | zero => simp [midsAux]
    | succ n =>
      simp only [List.length_cons] at hk
      rw [midsAux_cons, List.getElem?_cons_succ, List.take_succ_cons, hexInfra_midAccum_cons]
      exact ih _ _ n (by omega)


theorem hexJordan_verticesAux_getElem?_eq (m : ℂ) (h : ℤ) (ts : List ℤ) (k : ℕ)
    (hk : k ≤ ts.length) :
    (verticesAux m h ts)[k]?
      = some (hexInfra_midAccum m h (ts.take k)
          + halfStep (hexInfra_headAccum h (ts.take k))) := by
  induction ts generalizing m h k with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hk
    subst hk
    simp [verticesAux]
  | cons t ts ih =>
    cases k with
    | zero => simp [verticesAux]
    | succ n =>
      simp only [List.length_cons] at hk
      rw [verticesAux_cons, List.getElem?_cons_succ, List.take_succ_cons,
        hexInfra_midAccum_cons, hexInfra_headAccum_cons]
      exact ih _ _ n (by omega)


end StatMech.Universality
