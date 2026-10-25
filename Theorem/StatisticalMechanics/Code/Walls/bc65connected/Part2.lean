/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc65connected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc64coarseembed.Part5
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
import Instance.StatisticalMechanics.Code.Walls.bc65connected.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc65_cat2G_isTree : bc65_cat2G.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]; exact ⟨0, by decide⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide


theorem bc65_caterpillar2_leafCount :
    (univ.filter (fun v => 3 ≤ bc65_cat2G.degree v)).card = 2 ∧
    (univ.filter (fun v => bc65_cat2G.degree v = 1)).card = 4 := by
  constructor <;> decide


theorem bc65_caterpillar2_savings :
    (univ.filter (fun v => bc65_cat2G.degree v = 1)).card
      < 3 * (univ.filter (fun v => 3 ≤ bc65_cat2G.degree v)).card := by
  rw [bc65_caterpillar2_leafCount.1, bc65_caterpillar2_leafCount.2]; norm_num


end StatMech.Walls
