/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Walls.bcorcorridors.Part4
open Set SimpleGraph
open StatMech StatMech.Lattice


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option maxRecDepth 4000

set_option maxHeartbeats 800000


def bcor_reflIso : hypercubicLattice 2 ≃g hypercubicLattice 2 :=
  ⟨bcor_reflEquiv, fun {x y} ↦ bcor_refl_adj x y⟩

end StatMech.Walls
