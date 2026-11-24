module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
open Filter Topology SimpleGraph
open scoped BigOperators
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxSecantData.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open StatMech.Lattice


noncomputable def boxSecantSurface (d n : ℕ) : ℝ := (2 * d) * (2 * n + 1) ^ (d - 1)


noncomputable def boxSecantVolume (d n : ℕ) : ℝ := (d : ℝ) * (2 * n + 1) ^ d


end FK
end StatMech
