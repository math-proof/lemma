/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.binsinsertion.Part7
import Theorem.StatisticalMechanics.Code.Walls.binsclosure.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open StatMech.Ising StatMech.IsingFK


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 20000


def bins_touchPattern (n : ℕ) (B : Fin 3 → bins_Branch) :
    ConfigSpace (Subtype fun e => e ∈ bondFinsetTouch 2 n) :=
  fun e => decide (e.1 ∈ bins_branchEdges B)


end StatMech.Walls
