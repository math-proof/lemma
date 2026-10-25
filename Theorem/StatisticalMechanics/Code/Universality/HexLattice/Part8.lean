/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexLattice.Part8


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


namespace HexWalk

@[simp] theorem trivialWalk_startMid (a : ℂ) (h : ℤ) : (trivialWalk a h).startMid = a := rfl

@[simp] theorem trivialWalk_h0 (a : ℂ) (h : ℤ) : (trivialWalk a h).h0 = h := rfl

@[simp] theorem trivialWalk_turns (a : ℂ) (h : ℤ) : (trivialWalk a h).turns = [] := rfl


@[simp]
theorem trivialWalk_numVertices (a : ℂ) (h : ℤ) : (trivialWalk a h).numVertices = 1 := rfl


@[simp]
theorem trivialWalk_turning (a : ℂ) (h : ℤ) : (trivialWalk a h).turning = 0 := by
  simp [turning, turnCount, trivialWalk]


theorem trivialWalk_legalTurns (a : ℂ) (h : ℤ) : (trivialWalk a h).LegalTurns := by
  intro t ht; simp [trivialWalk] at ht


theorem trivialWalk_isSAW (a : ℂ) (h : ℤ) : (trivialWalk a h).IsSAW := by
  unfold IsSAW vertices; simp [trivialWalk]


theorem trivialWalk_isLegalSAW (a : ℂ) (h : ℤ) : (trivialWalk a h).IsLegalSAW :=
  ⟨trivialWalk_legalTurns a h, trivialWalk_isSAW a h⟩


theorem turnCount_append (a : ℂ) (h : ℤ) (s t : List ℤ) :
    turnCount ⟨a, h, s ++ t⟩ = turnCount ⟨a, h, s⟩ + turnCount ⟨a, h, t⟩ := by
  simp [turnCount, List.sum_append]


theorem turning_append (a : ℂ) (h : ℤ) (s t : List ℤ) :
    turning ⟨a, h, s ++ t⟩ = turning ⟨a, h, s⟩ + turning ⟨a, h, t⟩ := by
  simp only [turning, turnCount_append]
  push_cast
  ring


theorem turning_concat (a : ℂ) (h : ℤ) (s : List ℤ) (t : ℤ) :
    turning ⟨a, h, s ++ [t]⟩ = turning ⟨a, h, s⟩ + (Real.pi / 3) * (t : ℝ) := by
  rw [turning_append]
  congr 1
  simp [turning, turnCount]


end HexWalk
end StatMech.Universality
