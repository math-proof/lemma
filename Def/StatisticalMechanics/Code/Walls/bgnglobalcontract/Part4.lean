/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bptpartitioncount.Part2
import Theorem.StatisticalMechanics.Code.Walls.bgnglobalcontract.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bgn_Wedges : Finset (Sym2 (Fin 8)) :=
  {s(0, 1), s(0, 2), s(0, 3), s(0, 6), s(0, 7), s(1, 4), s(1, 5), s(1, 6), s(1, 7)}


def bgn_W : SimpleGraph (Fin 8) := SimpleGraph.fromEdgeSet (↑bgn_Wedges)

end StatMech.Walls
