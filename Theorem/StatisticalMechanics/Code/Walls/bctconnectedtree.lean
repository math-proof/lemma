/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bctconnectedtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bgeexploration.Part2
import Instance.StatisticalMechanics.Code.Walls.bctconnectedtree
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


theorem bct_fiberForest_adj_iff {β V : Type} {H : SimpleGraph V} {p q : β × V} :
    (bct_fiberForest β V H).Adj p q ↔ (p.1 = q.1 ∧ H.Adj p.2 q.2) := by
  unfold bct_fiberForest SimpleGraph.fromRel
  constructor
  · rintro ⟨hne, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨h1, h2⟩
    · exact ⟨h1.symm, H.symm h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun hpq => (H.ne_of_adj h2) (by rw [hpq]), Or.inl ⟨h1, h2⟩⟩


theorem bct_fiberForest_fst {β V : Type} {H : SimpleGraph V} {p q : β × V}
    (h : (bct_fiberForest β V H).Adj p q) : p.1 = q.1 := (bct_fiberForest_adj_iff.mp h).1


end StatMech.Walls
