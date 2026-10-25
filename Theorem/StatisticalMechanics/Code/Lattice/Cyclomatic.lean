/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Cyclomatic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite


namespace StatMech.Lattice

open SimpleGraph

variable {V : Type*}


theorem tree_card_edges {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (hG : G.IsTree) : G.edgeFinset.card + 1 = Fintype.card V :=
  hG.card_edgeFinset


theorem connected_card_edges_ge {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (hG : G.Connected) : Fintype.card V ≤ G.edgeFinset.card + 1 := by
  have h := hG.card_vert_le_card_edgeSet_add_one
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card] at h


theorem connected_card_edges_eq_iff_isAcyclic {G : SimpleGraph V} [Fintype V]
    [Fintype G.edgeSet] (hG : G.Connected) :
    G.edgeFinset.card + 1 = Fintype.card V ↔ G.IsAcyclic := by
  constructor
  · intro h
    refine SimpleGraph.IsTree.isAcyclic ?_
    rw [isTree_iff_connected_and_card]
    refine ⟨hG, ?_⟩
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card]
  · intro hac
    exact (SimpleGraph.IsTree.card_edgeFinset ⟨hG, hac⟩)


theorem connected_isTree_iff_card_edges {G : SimpleGraph V} [Fintype V]
    [Fintype G.edgeSet] (hG : G.Connected) :
    G.IsTree ↔ G.edgeFinset.card + 1 = Fintype.card V := by
  rw [connected_card_edges_eq_iff_isAcyclic hG]
  exact ⟨fun h => h.isAcyclic, fun h => ⟨hG, h⟩⟩


theorem exists_spanning_tree_card {G : SimpleGraph V} [Finite V]
    (hG : G.Connected) :
    ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ Nat.card T.edgeSet + 1 = Nat.card V := by
  obtain ⟨T, hle, hT⟩ := hG.exists_isTree_le
  exact ⟨T, hle, hT, ((isTree_iff_connected_and_card).mp hT).2⟩


end StatMech.Lattice
