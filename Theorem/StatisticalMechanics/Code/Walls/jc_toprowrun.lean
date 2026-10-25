/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_toprowrun.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc_earanchor.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Def.StatisticalMechanics.Code.Walls.jc_toprowrun
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc_shiftX_coord0 (c : Site 2) (j : ℤ) : (jc_shiftX c j) 0 = c 0 + j := by
  simp [jc_shiftX, Pi.add_apply]


theorem jc_shiftX_coord1 (c : Site 2) (j : ℤ) : (jc_shiftX c j) 1 = c 1 := by
  simp [jc_shiftX, Pi.add_apply]


theorem jc_shiftX_zero (c : Site 2) : jc_shiftX c 0 = c := by
  funext i; fin_cases i <;> simp [jc_shiftX, Pi.add_apply]


end Walls
end StatMech
