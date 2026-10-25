/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexLattice.Part7


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


namespace HexWalk

@[simp]
theorem turning_eq (w : HexWalk) : w.turning = (Real.pi / 3) * (w.turns.sum : ℝ) := rfl


end HexWalk
end StatMech.Universality
