/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc113boundaryforest.Part6
import Def.StatisticalMechanics.Code.Walls.bc114haschild
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]


variable {G : SimpleGraph V}


theorem bc114_isInternal_degree_ge_two (F : SimpleGraph V) [DecidableRel F.Adj] {v : V}
    (hv : bc114_IsInternal F v) : 2 ≤ F.degree v := by
  obtain ⟨s, t, p, i, hp, hi0, hilt, hveq⟩ := hv
  rw [← hveq]
  exact bc114_internal_degree_ge_two F p hp hi0 hilt


theorem bc114_leaf_not_internal (F : SimpleGraph V) [DecidableRel F.Adj] {v : V}
    (hdeg : F.degree v = 1) : ¬ bc114_IsInternal F v := by
  intro hv
  have := bc114_isInternal_degree_ge_two F hv
  omega


end StatMech.Walls
