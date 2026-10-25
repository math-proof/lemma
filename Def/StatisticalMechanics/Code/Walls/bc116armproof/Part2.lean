/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc114haschild.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc101mengergap
import Theorem.StatisticalMechanics.Code.Walls.bc116armproof.Part2
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


def bc116_ArmPathMembership (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    (B H : Site d → Prop) : Prop :=
  bc116_ThroughPathCovered (bc67_contractedLattice ω L y) B H


end StatMech.Walls
