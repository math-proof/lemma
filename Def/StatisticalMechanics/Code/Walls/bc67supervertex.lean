/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc67supervertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc66assembly
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc67_GnIncident (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d) : Prop :=
  ∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a


noncomputable def bc67_contractedLattice (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    SimpleGraph (Site d) :=
  openSubgraph d (removeSites (bc61_boxAround d L y) ω)


end StatMech.Walls
