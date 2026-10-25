/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Def.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part8
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


theorem clampCoord_bounds {a b x : ℝ} (hab : a ≤ b) :
    a ≤ clampCoord a b x ∧ clampCoord a b x ≤ b := by
  exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clampCoord_of_mem {a b x : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    clampCoord a b x = x := by
  rw [clampCoord, min_eq_right hxb, max_eq_right hax]

theorem clampCoord_of_le_left {a b x : ℝ} (hab : a ≤ b) (hx : x ≤ a) :
    clampCoord a b x = a := by
  rw [clampCoord, min_eq_right (hx.trans hab), max_eq_left hx]

theorem clampCoord_of_right_le {a b x : ℝ} (hab : a ≤ b) (hx : b ≤ x) :
    clampCoord a b x = b := by
  rw [clampCoord, min_eq_left hx, max_eq_right hab]


theorem eq_of_clampCoord_eq_interior {a b x y : ℝ} (hab : a < b)
    (hay : a < y) (hyb : y < b) (h : clampCoord a b x = y) : x = y := by
  by_cases hxa : x ≤ a
  · rw [clampCoord_of_le_left hab.le hxa] at h
    linarith
  by_cases hbx : b ≤ x
  · rw [clampCoord_of_right_le hab.le hbx] at h
    linarith
  rw [clampCoord_of_mem (le_of_not_ge hxa) (le_of_not_ge hbx)] at h
  exact h


end ContinuousRectangleCrossing
end StatMech
