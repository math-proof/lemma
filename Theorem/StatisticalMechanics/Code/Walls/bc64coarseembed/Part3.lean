/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc64coarseembed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc63coarseforest.Part2
import Instance.StatisticalMechanics.Code.Walls.bc64coarseembed.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc64_starForest_adj_iff {β : Type} {p q : β × Fin 4} :
    (bc64_starForest β).Adj p q ↔ (p.1 = q.1 ∧ bc64_starG.Adj p.2 q.2) := by
  unfold bc64_starForest SimpleGraph.fromRel
  constructor
  · rintro ⟨hne, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h1.symm, bc64_starG.symm h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun hpq => (bc64_starG.ne_of_adj h2) (by rw [hpq]), Or.inl ⟨h1, h2⟩⟩


theorem bc64_starForest_fst {β : Type} {p q : β × Fin 4} (h : (bc64_starForest β).Adj p q) :
    p.1 = q.1 := (bc64_starForest_adj_iff.mp h).1


end StatMech.Walls
