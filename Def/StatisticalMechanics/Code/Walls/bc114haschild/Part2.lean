/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc113boundaryforest.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc114haschild.Part2
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]


variable {G : SimpleGraph V}


def bc114_ArmCovered (F : SimpleGraph V) (B H : V → Prop) : Prop :=
  ∀ v, ¬ B v → ¬ H v → bc114_IsInternal F v


end StatMech.Walls
