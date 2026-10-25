/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc75spanningtree.Part4
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


def bc76_bufferResVec (L : ℕ) (y : Site d) : Fin d → Fin (4 * L + 1) :=
  fun i => ⟨(y i % (4 * L + 1 : ℤ)).toNat, by
    have hpos : (0 : ℤ) < 4 * L + 1 := by positivity
    have h1 : 0 ≤ y i % (4 * L + 1 : ℤ) := Int.emod_nonneg _ (by positivity)
    have h2 : y i % (4 * L + 1 : ℤ) < 4 * L + 1 := Int.emod_lt_of_pos _ hpos
    omega⟩


end StatMech.Walls
