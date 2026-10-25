/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bcrboxrep.Part2
import Theorem.StatisticalMechanics.Code.Walls.brtrouteclose
import Theorem.StatisticalMechanics.Code.Walls.brpreproute
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


noncomputable def brp_witArm (R : ℕ) (i : Fin 3) : Site 2 :=
  if i = 0 then bc57_pt (R : ℤ) 0 else if i = 1 then bc57_pt 0 (R : ℤ) else bc57_pt 0 (-(R : ℤ))

end StatMech.Walls
