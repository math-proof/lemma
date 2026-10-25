/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc112sepcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc110globalforest
import Theorem.StatisticalMechanics.Code.Walls.bc106separated.Part3
import Def.StatisticalMechanics.Code.Walls.bc112sepcontract.Part3
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


theorem bc112_shifts_ne_zero {k : ℤ} (hk : k ∈ bc112_shifts) : k ≠ 0 := by
  fin_cases hk <;> decide

theorem bc112_shifts_natAbs_le {k : ℤ} (hk : k ∈ bc112_shifts) {L : ℕ} (hL : 3 ≤ L) :
    k.natAbs ≤ L := by
  fin_cases hk <;> simp <;> omega


end StatMech.Walls
