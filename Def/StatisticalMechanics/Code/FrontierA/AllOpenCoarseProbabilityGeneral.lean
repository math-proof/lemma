/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundaryGeneral.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonBurtonKeane
import Theorem.StatisticalMechanics.Code.Walls.bc62coarseclose.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseProbabilityGeneral
open Finset Set SimpleGraph MeasureTheory Filter Topology
open scoped ENNReal BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open StatMech.Walls

variable {d : ℕ}


noncomputable def bgfdFaithfulAllOpenBoundaryCard
    (d L N : ℕ) : ℕ :=
  boxSV_boundaryCard d ((2 * L + 1) * N + L + 1)

end StatMech.FrontierA
