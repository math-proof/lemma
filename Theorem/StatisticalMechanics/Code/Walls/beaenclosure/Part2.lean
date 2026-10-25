/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.brpreproute.Part2
import Def.StatisticalMechanics.Code.Walls.beaenclosure.Part2
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


@[simp] theorem bea_arm_zero : bea_arm 0 = bc57_pt 12 1 := rfl

@[simp] theorem bea_arm_one : bea_arm 1 = bc57_pt 10 0 := rfl


theorem bea_repRoute_false :
    ¬ bcr_RepRoute bea_ce 1 (bc57_pt 0 0) bea_arm := by
  intro h
  have hreach := h 0 1 (by decide)
  rw [bea_arm_one, bea_arm_zero] at hreach
  exact bea_pinch hreach


theorem bea_genuineTrif_entry_false :
    btr_IsGenuineCoarseTrif bea_ce 1 (bc57_pt 0 0) ∧
      ¬ (bc67_contractedLattice bea_ce 1 (bea_arm 1)).Reachable (bc57_pt 0 0) (bea_arm 0) ∧
      ¬ bcr_RepRoute bea_ce 1 (bc57_pt 0 0) bea_arm := by
  refine ⟨bea_genuineTrif, ?_, bea_repRoute_false⟩
  rw [bea_arm_one, bea_arm_zero]
  exact bea_pinch

#check @bea_genuineTrif_entry_false

end StatMech.Walls
