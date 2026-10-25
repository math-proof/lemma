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
import Def.StatisticalMechanics.Code.Universality.HexStripBandClose.Part4


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexJordan_six_left_not_saw (a : ℂ) (h0 : ℤ) (s r : List ℤ)
    (hsaw : (ofTurns a h0 (s ++ ([(1 : ℤ), 1, 1, 1, 1, 1] ++ r))).IsSAW) : False := by
  set ts := s ++ ([(1 : ℤ), 1, 1, 1, 1, 1] ++ r) with hts
  have hk1 : ts.take s.length = s := by rw [hts, List.take_append]; simp
  have hk2 : ts.take (s.length + 6) = s ++ [(1 : ℤ), 1, 1, 1, 1, 1] := by
    rw [hts, List.take_append]; simp
  have hpos : hexJordan_vertexPos a h0 ts s.length
      = hexJordan_vertexPos a h0 ts (s.length + 6) := by
    unfold hexJordan_vertexPos
    rw [hk1, hk2, hexJordan_midAccum_append, hexJordan_headAccum_append,
      hexJordan_midAccum_six_left]
    have hh : hexInfra_headAccum (hexInfra_headAccum h0 s) [(1 : ℤ), 1, 1, 1, 1, 1]
        = hexInfra_headAccum h0 s + 6 := by
      simp only [hexInfra_headAccum_cons, hexInfra_headAccum_nil]; ring
    rw [hh, hexStrip_halfStep_add6]
  have hlen : s.length + 6 ≤ ts.length := by
    rw [hts]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  exact hexJordan_vertexPos_ne_of_saw a h0 ts hsaw s.length (s.length + 6) (by omega) hlen
    (by omega) hpos


theorem hexJordan_six_right_not_saw (a : ℂ) (h0 : ℤ) (s r : List ℤ)
    (hsaw : (ofTurns a h0 (s ++ ([(-1 : ℤ), -1, -1, -1, -1, -1] ++ r))).IsSAW) : False := by
  set ts := s ++ ([(-1 : ℤ), -1, -1, -1, -1, -1] ++ r) with hts
  have hk1 : ts.take s.length = s := by rw [hts, List.take_append]; simp
  have hk2 : ts.take (s.length + 6) = s ++ [(-1 : ℤ), -1, -1, -1, -1, -1] := by
    rw [hts, List.take_append]; simp
  have hpos : hexJordan_vertexPos a h0 ts s.length
      = hexJordan_vertexPos a h0 ts (s.length + 6) := by
    unfold hexJordan_vertexPos
    rw [hk1, hk2, hexJordan_midAccum_append, hexJordan_headAccum_append,
      hexJordan_midAccum_six_right]
    have hh : hexInfra_headAccum (hexInfra_headAccum h0 s) [(-1 : ℤ), -1, -1, -1, -1, -1]
        = hexInfra_headAccum h0 s - 6 := by
      simp only [hexInfra_headAccum_cons, hexInfra_headAccum_nil]; ring
    rw [hh, show hexInfra_headAccum h0 s - 6 = (hexInfra_headAccum h0 s - 6) from rfl,
      show (hexInfra_headAccum h0 s - 6 : ℤ) = (hexInfra_headAccum h0 s - 6) from rfl]
    rw [show (hexInfra_headAccum h0 s - 6 : ℤ) = (hexInfra_headAccum h0 s - 6) from rfl]
    have : HexWalk.halfStep (hexInfra_headAccum h0 s - 6)
        = HexWalk.halfStep (hexInfra_headAccum h0 s) := by
      rw [show (hexInfra_headAccum h0 s - 6 : ℤ) = (hexInfra_headAccum h0 s - 6) + 6 - 6 from by
        ring]
      rw [show (hexInfra_headAccum h0 s - 6 + 6 - 6 : ℤ) = hexInfra_headAccum h0 s - 6 from by ring]
      have h6 := hexStrip_halfStep_add6 (hexInfra_headAccum h0 s - 6)
      rw [show (hexInfra_headAccum h0 s - 6 + 6 : ℤ) = hexInfra_headAccum h0 s from by ring] at h6
      exact h6.symm
    rw [this]
  have hlen : s.length + 6 ≤ ts.length := by
    rw [hts]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  exact hexJordan_vertexPos_ne_of_saw a h0 ts hsaw s.length (s.length + 6) (by omega) hlen
    (by omega) hpos


end StatMech.Universality
