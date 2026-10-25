/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc57coarsetrif.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc54coarse
import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc58wholebox.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc58_p (a b : ℤ) : Site 2 := ![a, b]

end StatMech.Walls
