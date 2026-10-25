/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.FK.OrderTransition.Part2
import Theorem.StatisticalMechanics.Code.FK.OrderContour
open Finset Set SimpleGraph Filter Topology
open scoped BigOperators NNReal

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice


noncomputable def peierlsTail (q : ℝ) (N : ℕ) : ℝ :=
  ∑' n, peierlsContourWeight q (n + N)


end FK
end StatMech
