/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bskspanningtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bctconnectedtree.Part3
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


theorem bsk_exists_spanningTree {V : Type*} (G : SimpleGraph V) (h : G.Connected) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree :=
  h.exists_isTree_le


theorem bsk_three_le_degree {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {v a b c : W}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c) : 3 ≤ G.degree v := by
  have hsub : ({a, b, c} : Finset W) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;>
      simp only [SimpleGraph.mem_neighborFinset, ha, hb, hc]
  have hcard : ({a, b, c} : Finset W).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  calc 3 = ({a, b, c} : Finset W).card := hcard.symm
    _ ≤ (G.neighborFinset v).card := Finset.card_le_card hsub
    _ = G.degree v := rfl


end StatMech.Walls
