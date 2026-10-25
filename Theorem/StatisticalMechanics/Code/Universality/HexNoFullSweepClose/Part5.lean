/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexNoFullSweepClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Def.StatisticalMechanics.Code.Universality.HexNoFullSweepClose.Part3


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexSweep_simplyConnected_trivial_bound (a : ℂ) (h0 : ℤ) :
    |hexInfra_headAccum h0 ([] : List ℤ) - (hexSweep_simplyConnected_trivial a h0).H| < 6 := by
  refine hexSweep_bound (fun m => m = a) a h0 a (hexSweep_simplyConnected_trivial a h0)
    ([] : List ℤ) ?_
  refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
  intro m hm
  have hmids : (HexWalk.ofTurns a h0 ([] : List ℤ)).mids = [a] := by
    unfold HexWalk.mids HexWalk.ofTurns; simp only [HexWalk.midsAux_nil]
  rw [hmids, List.mem_singleton] at hm; exact hm


theorem hexSweep_six_left_not_saw (a : ℂ) (h0 : ℤ) (s r : List ℤ)
    (hsaw : (ofTurns a h0 (s ++ ([(1 : ℤ), 1, 1, 1, 1, 1] ++ r))).IsSAW) : False := by
  set ts := s ++ ([(1 : ℤ), 1, 1, 1, 1, 1] ++ r) with hts
  have hlen : s.length + 6 ≤ ts.length := by
    rw [hts]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  
  have hdrop : ts.drop s.length = [(1 : ℤ), 1, 1, 1, 1, 1] ++ r := by
    rw [hts, List.drop_append_of_le_length (le_refl _)]; simp
  have hmono : ∀ k, s.length ≤ k → k < s.length + 6 → ts[k]?.getD 0 = 1 := by
    intro k hk hk'
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hek : ts[s.length + n]? = (ts.drop s.length)[n]? := (List.getElem?_drop).symm
    rw [hek, hdrop]
    have hn6 : n < 6 := by omega
    interval_cases n <;> rfl
  have hpos := hexSweep_vertexPos_eq_of_six_left a h0 ts s.length hlen hmono
  exact hexJordan_vertexPos_ne_of_saw a h0 ts hsaw s.length (s.length + 6) (by omega) hlen
    (by omega) hpos


theorem hexSweep_nonMonotone_revolution_pair (h0 : ℤ) :
    hexStripWinding_runningHead h0 [(1 : ℤ), 1, 1, 1, 1, 1, 1, -1] 8
      = hexStripWinding_runningHead h0 [(1 : ℤ), 1, 1, 1, 1, 1, 1, -1] 0 + 6 := by
  simp [hexStripWinding_runningHead]

end StatMech.Universality
