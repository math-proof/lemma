module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.bc58wholebox.Part4
public import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
public import Theorem.StatisticalMechanics.Code.Walls.bc59corridors
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
set_option linter.style.longLine false
set_option maxRecDepth 4000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc59_HasDisjointCorridors (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, bc59_DisjointCorridors ω


end StatMech.Walls
