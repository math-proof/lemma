/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc5_earframe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
import Theorem.StatisticalMechanics.Code.Walls.jc3_shelfcell
import Def.StatisticalMechanics.Code.Walls.jc5_earframe
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


@[simp] theorem jc5_earCell_eq (c : Site 2) (len : ℤ) :
    jc5_earCell c len = c + ![len, 0] := rfl


theorem jc5_earCell_eq_runRightEnd (c : Site 2) (len : ℤ) :
    jc5_earCell c len = jc3_runRightEnd c len := rfl


theorem jc5_earCell_coord1 (c : Site 2) (len : ℤ) :
    (jc5_earCell c len) 1 = c 1 := by
  rw [jc5_earCell_eq]
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; ring


end Walls
end StatMech
