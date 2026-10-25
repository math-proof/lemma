/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc_runnoup
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Def.StatisticalMechanics.Code.Walls.jc2_thickshelf
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


@[simp] theorem jc2_downCell_eq (v : Site 2) : jc2_downCell v = v + ![0, -1] := rfl


theorem jc2_downCell_run (c : Site 2) (j : ℤ) :
    jc2_downCell (c + ![j, 0]) = c + ![j, -1] := by
  funext k; fin_cases k <;> · simp only [jc2_downCell, Pi.add_apply]; simp


theorem jc2_shelfCell_coord1 (c : Site 2) (j : ℤ) :
    (c + ![j, -1] : Site 2) 1 = c 1 - 1 := by
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; ring


theorem jc2_shelfCell_coord0 (c : Site 2) (j : ℤ) :
    (c + ![j, -1] : Site 2) 0 = c 0 + j := by
  simp only [Pi.add_apply, Matrix.cons_val_zero]


end Walls
end StatMech
