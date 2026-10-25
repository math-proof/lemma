/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bptpartitioncount.Part2
import Theorem.StatisticalMechanics.Code.Walls.bgnglobalcontract
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


def bgn_boundaryClass (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (u a : Site d) : Set (Site d) :=
  {c | c ∈ (bgn_idx L) '' (vertexBoundary d R) ∧ (bkg_deleteVertex (bgn_Gn ω L) u).Reachable a c}


end StatMech.Walls
