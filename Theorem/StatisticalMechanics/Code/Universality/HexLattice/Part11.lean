/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexLattice.Part11


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


open HexWalk


theorem trivialWalk_endMid (a : ℂ) (h0 : ℤ) : HexWalk.endMid (trivialWalk a h0) = a := by
  unfold HexWalk.endMid
  have : (trivialWalk a h0).mids = [a] := by
    unfold HexWalk.mids; simp [trivialWalk]
  simp [this]


theorem parafSummand_self (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (σ x : ℝ)
    (hreg : region a) :
    parafSummand region a h0 a σ x [] = (x : ℂ) := by
  have hofeq : ofTurns a h0 [] = trivialWalk a h0 := rfl
  have hmids : (trivialWalk a h0).mids = [a] := by
    unfold HexWalk.mids; simp [trivialWalk]
  unfold parafSummand
  rw [if_pos]
  · have hturn : (trivialWalk a h0).turning = 0 := trivialWalk_turning a h0
    have hnum : (trivialWalk a h0).numVertices = 1 := rfl
    rw [hofeq, hturn, hnum]
    simp
  · rw [hofeq]
    refine ⟨trivialWalk_isLegalSAW a h0, ?_, trivialWalk_endMid a h0⟩
    intro m hm
    rw [hmids] at hm
    simp only [List.mem_singleton] at hm
    rw [hm]; exact hreg

end StatMech.Universality
