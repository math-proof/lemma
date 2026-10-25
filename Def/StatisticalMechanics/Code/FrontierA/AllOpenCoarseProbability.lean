/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundary.Part3
import Theorem.StatisticalMechanics.Code.Walls.bdcdetcount.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc62coarseclose.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseProbability
open Finset Set SimpleGraph MeasureTheory Filter Topology
open scoped ENNReal BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open StatMech.Walls


noncomputable def faithfulAllOpenBoundaryCard (L N : ℕ) : ℕ :=
  boxSV_boundaryCard 2 ((2 * L + 1) * N + L + 1)

end StatMech.FrontierA
