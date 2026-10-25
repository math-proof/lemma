/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc63coarseforest.Part2
import Instance.StatisticalMechanics.Code.Walls.bc64coarseembed.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc64_starG_isTree : bc64_starG.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  exact ⟨by rw [SimpleGraph.connected_iff_exists_forall_reachable]; exact ⟨0, by decide⟩,
    by rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide⟩


theorem bc64_starG_centre_deg : bc64_starG.degree 0 = 3 := by decide


theorem bc64_starG_leaf_deg : ∀ i : Fin 4, i ≠ 0 → bc64_starG.degree i = 1 := by decide


theorem bc64_starG_deg1_iff (i : Fin 4) : bc64_starG.degree i = 1 ↔ i ≠ 0 := by
  constructor
  · intro h; rintro rfl; rw [bc64_starG_centre_deg] at h; exact absurd h (by decide)
  · exact bc64_starG_leaf_deg i


end StatMech.Walls
