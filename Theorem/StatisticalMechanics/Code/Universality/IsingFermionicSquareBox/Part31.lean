/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareCompletedLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch
        (fkIsingSquareCompletedLoopGraph n hn (setClosed e.1 omega))
        (.dart (e, .west)) (.dart (e, .south))
        (.dart (e, .east)) (.dart (e, .north)) := by
  rw [fkIsingSquareCompletedLoopGraph,
    fkIsingSquareLoopGraph_setOpen_eq_twoEdgeSwitch]
  ext x y
  cases x <;> cases y <;>
    simp [fkIsingSquareCompletedLoopGraph, medialTwoEdgeSwitch,
      SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
      SimpleGraph.edge_adj]

theorem fkIsingSquareCompletedLoopGraph_reachable_source_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    (fkIsingSquareCompletedLoopGraph n hn omega).Reachable .source z ↔
      (fkIsingSquareLoopGraph n hn omega).Reachable .source z := by
  rw [fkIsingSquareCompletedLoopGraph, reachable_sup_edge_iff]
  constructor
  · rintro (h | ⟨_, hterminal⟩ | ⟨_, hsource⟩)
    · exact h
    · exact (fkIsingSquareLoopGraph_source_reachable_terminal
        n hn omega).trans hterminal
    · exact hsource
  · exact Or.inl

theorem fkIsingSquareCompletedLoopGraph_source_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareCompletedLoopGraph n hn omega).degree .source = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareCompletedLoopGraph n hn omega).neighborFinset .source =
        {.dart (fkIsingSquareSourceInteriorDart n hn), .terminal} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareCompletedLoopGraph,
      fkIsingSquareLoopGraph_adj_source_iff, SimpleGraph.edge_adj,
      fkIsingSquare_source_ne_terminal n]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, by simp⟩
  rw [hfin]
  simp

theorem fkIsingSquareCompletedLoopGraph_terminal_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareCompletedLoopGraph n hn omega).degree .terminal = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareCompletedLoopGraph n hn omega).neighborFinset .terminal =
        {.dart (fkIsingSquareTerminalInteriorDart n hn), .source} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareCompletedLoopGraph,
      fkIsingSquareLoopGraph_adj_terminal_iff, SimpleGraph.edge_adj]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, by simp⟩
  rw [hfin]
  simp

theorem fkIsingSquareCompletedLoopGraph_dart_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareCompletedLoopGraph n hn omega).degree (.dart d) = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareCompletedLoopGraph n hn omega).neighborFinset (.dart d) =
        (fkIsingSquareLoopGraph n hn omega).neighborFinset (.dart d) := by
    ext z
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareCompletedLoopGraph, SimpleGraph.edge_adj]
  rw [hfin, SimpleGraph.card_neighborFinset_eq_degree,
    fkIsingSquareLoopGraph_dart_degree]

theorem fkIsingSquareCompletedLoopGraph_even_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    Even ((fkIsingSquareCompletedLoopGraph n hn omega).degree z) := by
  cases z with
  | source =>
      rw [fkIsingSquareCompletedLoopGraph_source_degree n hn omega]
      exact even_two
  | terminal =>
      rw [fkIsingSquareCompletedLoopGraph_terminal_degree n hn omega]
      exact even_two
  | dart d =>
      rw [fkIsingSquareCompletedLoopGraph_dart_degree n hn omega d]
      exact even_two


end
end StatMech.Universality
