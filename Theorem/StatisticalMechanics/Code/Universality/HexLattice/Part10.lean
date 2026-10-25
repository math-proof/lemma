/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexLattice.Part10


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


open HexWalk


@[simp]
theorem hexZSummand_nil (a : ℂ) (h0 : ℤ) (x : ℝ) :
    hexZSummand a h0 x [] = ENNReal.ofReal x := by
  unfold hexZSummand
  rw [if_pos]
  · simp
  · exact trivialWalk_isLegalSAW a h0


end StatMech.Universality
