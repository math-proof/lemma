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
import Def.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc2_block2_fullyThick : jc2_FullyThick jc2_block2 (![0, 1] : Site 2) 1 := by
  intro j hj0 hj1
  rw [jc2_downCell_run]
  
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
    · refine ⟨?_, ?_⟩
      · simp only [Pi.add_apply, Matrix.cons_val_zero]; omega
      · left; simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]; ring


theorem jc2_block2_shelf_mem :
    ∀ j : ℤ, 0 ≤ j → j ≤ 1 → ((![0, 1] : Site 2) + ![j, -1]) ∈ jc2_block2 :=
  jc2_shelf_mem jc2_block2 (![0, 1] : Site 2) 1 jc2_block2_fullyThick

end Walls
end StatMech
