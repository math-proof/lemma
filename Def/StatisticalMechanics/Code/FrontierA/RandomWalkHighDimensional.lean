/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RandomWalkHighDimensional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.RandomWalkHighDimensionalReduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice


def latticeOriginDelta (d : ℕ) : Site d → ℝ :=
  fun x => if x = 0 then 1 else 0


noncomputable def latticeEuclideanRadius (d : ℕ) (x : Site d) : ℝ :=
  Real.sqrt (∑ i, (x i : ℝ) ^ 2)


end StatMech.FrontierA
