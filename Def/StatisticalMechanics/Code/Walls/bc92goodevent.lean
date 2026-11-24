module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.bc91hcanonfree
public import Theorem.StatisticalMechanics.Code.Walls.bc85bootstrap
public import Theorem.StatisticalMechanics.Code.Walls.bc78mergedichotomy
public import Theorem.StatisticalMechanics.Code.Walls.bc75spanningtree.Part4
public import Theorem.StatisticalMechanics.Code.Walls.bc62coarseclose.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc92goodevent.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc92_GoodEvent (L R : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | bc73_SublatticeForest ω L R}


end StatMech.Walls
