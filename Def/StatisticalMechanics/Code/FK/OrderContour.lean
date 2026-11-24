module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.FK.OrderTransition.Part2
open Finset Set SimpleGraph Filter Topology
open scoped BigOperators NNReal
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open StatMech.Lattice


noncomputable def peierlsContourWeight (q : ℝ) (n : ℕ) : ℝ := (4 / q) ^ n

end FK
end StatMech
