/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/beaenclosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.brpreproute.Part2
import Theorem.StatisticalMechanics.Code.Walls.beaenclosure
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


noncomputable def bea_arm (i : Fin 3) : Site 2 :=
  if i = 0 then bc57_pt 12 1 else if i = 1 then bc57_pt 10 0 else bc57_pt 2 (-1)

end StatMech.Walls
