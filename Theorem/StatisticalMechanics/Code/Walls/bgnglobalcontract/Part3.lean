/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgnglobalcontract.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bptpartitioncount.Part2
import Def.StatisticalMechanics.Code.Walls.bgnglobalcontract.Part3
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


theorem bgn_reach_isolated {V : Type*} {H : SimpleGraph V} {u : V}
    (hiso : ∀ z, ¬ H.Adj u z) {a : V} (h : H.Reachable a u) : a = u := by
  obtain ⟨w⟩ := h.symm
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hiso _)


end StatMech.Walls
