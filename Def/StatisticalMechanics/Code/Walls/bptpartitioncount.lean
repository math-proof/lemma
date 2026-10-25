/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bsdsepdegree
import Theorem.StatisticalMechanics.Code.Walls.bc69count.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkgclassicalforest.Part2
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


def bpt_boundaryClass (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (x a : Site d) : Set (Site d) :=
  {c | c ∈ vertexBoundary d R ∧ (bc67_contractedLattice ω L x).Reachable a c}


end StatMech.Walls
