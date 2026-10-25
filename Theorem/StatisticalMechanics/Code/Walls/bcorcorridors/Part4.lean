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
import Def.StatisticalMechanics.Code.Walls.bcorcorridors.Part3
open Set SimpleGraph
open StatMech StatMech.Lattice


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option maxRecDepth 4000

set_option maxHeartbeats 800000


theorem bcor_refl_adj (x y : Site 2) :
    (hypercubicLattice 2).Adj (bcor_reflFun x) (bcor_reflFun y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [bcor_reflFun, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show -x 1 - -y 1 = -(x 1 - y 1) by ring, Int.natAbs_neg]


end StatMech.Walls
