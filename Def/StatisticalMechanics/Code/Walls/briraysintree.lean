module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.bcaconcreteclose
public import Theorem.StatisticalMechanics.Code.Walls.bararmray
public import Theorem.StatisticalMechanics.Code.Walls.briraysintree
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bri_rayEdges {V : Type*} (r : ℕ → V) (N : ℕ) : Set (Sym2 V) :=
  {e | ∃ k < N, e = s(r k, r (k + 1))}


def bri_rayGraph {V : Type*} (r : ℕ → V) (N : ℕ) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (bri_rayEdges r N)


end StatMech.Walls
