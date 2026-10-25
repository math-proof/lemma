/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc75spanningtree.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc76buffer
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc76_yBuf (L : ℕ) : Site 2 := bc57_pt (4 * (L : ℤ) + 1) 0


noncomputable def bc76_twoBoxCollapse (L : ℕ) : Site 2 → Site 2 :=
  fun x => if x ∈ bc61_boxAround 2 L (0 : Site 2) then (0 : Site 2)
           else if x ∈ bc61_boxAround 2 L (bc76_yBuf L) then bc76_yBuf L
           else x


noncomputable def bc76_twoBoxGn (L : ℕ) : SimpleGraph (Site 2) :=
  bc72_quotGraph (openSubgraph 2 bc60_upperLines) (bc76_twoBoxCollapse L)


end StatMech.Walls
