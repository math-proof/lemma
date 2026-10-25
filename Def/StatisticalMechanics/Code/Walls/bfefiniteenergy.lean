/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfefiniteenergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfin2assemble
import Theorem.StatisticalMechanics.Code.Walls.bftfinetrif.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc67supervertex.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc62coarseclose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bpeprobcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc120closure
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bfefiniteenergy
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


def bfe_finiteEnergy_residue (μ : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  bc61_CoarseTrifExistence μ 0


end StatMech.Walls
