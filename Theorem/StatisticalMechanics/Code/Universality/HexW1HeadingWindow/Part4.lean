/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
import Def.StatisticalMechanics.Code.Universality.HexW1HeadingWindow.Part2


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexW1_trivialWindingBound_toBoundarySide_heading (a : ℂ) (h0 : ℤ) :
    hexInfra_headAccum h0 ([] : List ℤ) = (hexW1_trivialWindingBound a h0).toBoundarySide.H := by
  have hadm : (HexWalk.ofTurns a h0 ([] : List ℤ)).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ([] : List ℤ)).StaysIn (fun m => m = a)
      ∧ (HexWalk.ofTurns a h0 ([] : List ℤ)).EndsAt a := by
    refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
    intro m hm
    have hmids : (HexWalk.ofTurns a h0 ([] : List ℤ)).mids = [a] := by
      unfold HexWalk.mids HexWalk.ofTurns; simp only [HexWalk.midsAux_nil]
    rw [hmids, List.mem_singleton] at hm; exact hm
  exact (hexW1_trivialWindingBound a h0).toBoundarySide.heading_det ([] : List ℤ) hadm


theorem hexW1_trivialWindingBound_turning_zero (a : ℂ) (h0 : ℤ) :
    (HexWalk.ofTurns a h0 ([] : List ℤ)).turning = 0 := by
  have hadm : (HexWalk.ofTurns a h0 ([] : List ℤ)).IsLegalSAW
      ∧ (HexWalk.ofTurns a h0 ([] : List ℤ)).StaysIn (fun m => m = a)
      ∧ (HexWalk.ofTurns a h0 ([] : List ℤ)).EndsAt a := by
    refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
    intro m hm
    have hmids : (HexWalk.ofTurns a h0 ([] : List ℤ)).mids = [a] := by
      unfold HexWalk.mids HexWalk.ofTurns; simp only [HexWalk.midsAux_nil]
    rw [hmids, List.mem_singleton] at hm; exact hm
  have hkey := (hexW1_trivialWindingBound a h0).toBoundarySide.turning_const ([] : List ℤ) hadm
  have hH : (hexW1_trivialWindingBound a h0).toBoundarySide.H = h0 := rfl
  rw [hH] at hkey
  rw [hkey]; ring

end StatMech.Universality
