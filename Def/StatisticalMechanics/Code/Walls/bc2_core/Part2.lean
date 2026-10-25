/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CorridorSidesFromClusters.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcedpathconn
import Theorem.StatisticalMechanics.Code.Walls.bc2_cutunbounded
import Theorem.StatisticalMechanics.Code.Walls.bc2_forcemono
import Theorem.StatisticalMechanics.Code.Walls.bc2_raydisjoint.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc2_threewitnesses
import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc2_BoxForcedCorridorRouting (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, bc2_ForcedCorridorRouting ω


end Walls
end StatMech
