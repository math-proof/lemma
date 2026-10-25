/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.bc113boundaryforest.Part2
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem bc113_parent_spec (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    {v : V} (hv : ¬ B v) :
    G.Adj v (bc113_parent G B hreach v) ∧
      bc113_toB G B (bc113_parent G B hreach v) < bc113_toB G B v := by
  classical
  simp only [bc113_parent, dif_pos hv]
  exact (bc113_exists_parent G B hreach hv).choose_spec

end StatMech.Walls
