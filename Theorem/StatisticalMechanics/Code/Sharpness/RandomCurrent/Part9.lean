/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part7
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp]
theorem percolationField_apply (n : Current V) (e : Sym2 V) :
    percolationField n e = true ↔ 1 ≤ n e := by
  simp [percolationField]


theorem currentSubgraph_eq_percolationField (n : Current V) :
    currentSubgraph G n =
      G ⊓ SimpleGraph.fromEdgeSet {e | percolationField n e = true} := by
  ext x y
  simp only [currentSubgraph_adj, inf_adj, fromEdgeSet_adj, Set.mem_setOf_eq,
    percolationField_apply]
  constructor
  · rintro ⟨hadj, hpos⟩
    exact ⟨hadj, hpos, hadj.ne⟩
  · rintro ⟨hadj, hpos, _⟩
    exact ⟨hadj, hpos⟩


theorem currentConnected_iff_percolationField (n : Current V) (x y : V) :
    CurrentConnected G n x y ↔
      (G ⊓ SimpleGraph.fromEdgeSet {e | percolationField n e = true}).Reachable x y := by
  rw [CurrentConnected, currentSubgraph_eq_percolationField]


end Sharpness
end StatMech
