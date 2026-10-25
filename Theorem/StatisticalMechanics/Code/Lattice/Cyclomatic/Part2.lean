/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Cyclomatic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Def.StatisticalMechanics.Code.Lattice.Cyclomatic


namespace StatMech.Lattice

open SimpleGraph

variable {V : Type*}


theorem cyclomaticNumber_eq_zero_iff_isAcyclic {G : SimpleGraph V} [Fintype V]
    [Fintype G.edgeSet] (hG : G.Connected) :
    cyclomaticNumber G = 0 ↔ G.IsAcyclic := by
  unfold cyclomaticNumber
  rw [Nat.sub_eq_zero_iff_le]
  constructor
  · intro h
    have heq : G.edgeFinset.card + 1 = Fintype.card V :=
      le_antisymm h (connected_card_edges_ge hG)
    exact (connected_card_edges_eq_iff_isAcyclic hG).mp heq
  · intro hac
    rw [(connected_card_edges_eq_iff_isAcyclic hG).mpr hac]


theorem card_edges_eq_cyclomaticNumber_add {G : SimpleGraph V} [Fintype V]
    [Fintype G.edgeSet] (hG : G.Connected) :
    G.edgeFinset.card + 1 = Fintype.card V + cyclomaticNumber G := by
  have hge := connected_card_edges_ge hG
  unfold cyclomaticNumber
  omega


theorem not_isAcyclic_iff_exists_cycle {G : SimpleGraph V} :
    ¬ G.IsAcyclic ↔ ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  unfold SimpleGraph.IsAcyclic
  push Not
  rfl


theorem cyclomaticNumber_pos_iff_exists_cycle {G : SimpleGraph V} [Fintype V]
    [Fintype G.edgeSet] (hG : G.Connected) :
    0 < cyclomaticNumber G ↔ ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  rw [← not_isAcyclic_iff_exists_cycle, ← cyclomaticNumber_eq_zero_iff_isAcyclic hG,
    Nat.pos_iff_ne_zero]


end StatMech.Lattice
