/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc113boundaryforest.Part2
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]


open Classical in


noncomputable def bc113_parent (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B)
    (v : V) : V := by
  classical
  exact if h : ¬ B v then (bc113_exists_parent G B hreach h).choose else v


end StatMech.Walls
