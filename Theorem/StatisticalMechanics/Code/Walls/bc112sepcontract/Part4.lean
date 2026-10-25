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
import Def.StatisticalMechanics.Code.Walls.bc112sepcontract.Part4
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


theorem bc112_mem_hubs {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ} {y : Site d} :
    y ∈ bc112_hubs ω L R ↔ y ∈ box d R ∧ bc106_SeparatedCoarseTrif ω L y := by
  classical
  unfold bc112_hubs bc106_separatedTrifFinset
  rw [Finset.mem_filter, bc61_mem_coarseTrifFinset, bc106_SeparatedCoarseTrif]
  tauto


theorem bc112_hubs_boxes_disjoint {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ} {y z : Site d}
    (hy : y ∈ bc112_hubs ω L R) (hz : z ∈ bc112_hubs ω L R) (hne : y ≠ z) :
    Disjoint (bc61_boxAround d L y) (bc61_boxAround d L z) := by
  rw [bc112_mem_hubs] at hy hz
  exact bc106_boxes_disjoint hy.2 hz.2 hne


end StatMech.Walls
