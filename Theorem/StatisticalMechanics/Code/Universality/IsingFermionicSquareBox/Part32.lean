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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part29


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem mem_fkIsingSquareExplorationFinset_iff (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    z ∈ fkIsingSquareExplorationFinset n hn omega ↔
      (fkIsingSquareLoopGraph n hn omega).Reachable .source z := by
  simp [fkIsingSquareExplorationFinset]


theorem fkIsingSquare_open_local_mem_of_closed_west_mem_not_east
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega))
    (heast : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∉
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)) :
    ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn (setOpen e.1 omega) := by
  let G := fkIsingSquareCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  have hsourceWest : G.Reachable .source W := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Reachable .source (.dart (e, .west))
    rw [fkIsingSquareCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareExplorationFinset_iff]
    exact hwest
  have hwestEast : ¬ G.Reachable W E := by
    intro h
    apply heast
    rw [mem_fkIsingSquareExplorationFinset_iff,
      ← fkIsingSquareCompletedLoopGraph_reachable_source_iff]
    exact hsourceWest.trans h
  have hwestSouth : G.Adj W S := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .west)) (.dart (e, .south))
    apply Or.inl
    exact Or.inl ⟨(e, .west), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have heastNorth : G.Adj E N := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .east)) (.dart (e, .north))
    apply Or.inl
    exact Or.inl ⟨(e, .east), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have hall := medialTwoEdgeSwitch_reachable_all_of_reachable_left G
    (fkIsingSquareCompletedLoopGraph_even_degree n hn
      (setClosed e.1 omega))
    hwestSouth heastNorth hwestEast hsourceWest
  rw [← fkIsingSquareCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    n hn omega e] at hall
  intro side
  rw [mem_fkIsingSquareExplorationFinset_iff,
    ← fkIsingSquareCompletedLoopGraph_reachable_source_iff]
  cases side
  · exact hall.1
  · exact hall.2.2.1
  · exact hall.2.1
  · exact hall.2.2.2


theorem fkIsingSquare_open_local_mem_of_closed_east_mem_not_west
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (heast : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega))
    (hwest : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∉
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)) :
    ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn (setOpen e.1 omega) := by
  let G := fkIsingSquareCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  have hsourceEast : G.Reachable .source E := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Reachable .source (.dart (e, .east))
    rw [fkIsingSquareCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareExplorationFinset_iff]
    exact heast
  have hwestEast : ¬ G.Reachable W E := by
    intro h
    apply hwest
    rw [mem_fkIsingSquareExplorationFinset_iff,
      ← fkIsingSquareCompletedLoopGraph_reachable_source_iff]
    exact hsourceEast.trans h.symm
  have hwestSouth : G.Adj W S := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .west)) (.dart (e, .south))
    apply Or.inl
    exact Or.inl ⟨(e, .west), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have heastNorth : G.Adj E N := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .east)) (.dart (e, .north))
    apply Or.inl
    exact Or.inl ⟨(e, .east), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have hall := medialTwoEdgeSwitch_reachable_all_of_reachable_right G
    (fkIsingSquareCompletedLoopGraph_even_degree n hn
      (setClosed e.1 omega))
    hwestSouth heastNorth hwestEast hsourceEast
  rw [← fkIsingSquareCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    n hn omega e] at hall
  intro side
  rw [mem_fkIsingSquareExplorationFinset_iff,
    ← fkIsingSquareCompletedLoopGraph_reachable_source_iff]
  cases side
  · exact hall.1
  · exact hall.2.2.1
  · exact hall.2.1
  · exact hall.2.2.2


theorem fkIsingSquare_open_local_not_mem_of_closed_west_east_not_mem
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∉
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega))
    (heast : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∉
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)) :
    ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∉
      fkIsingSquareExplorationFinset n hn (setOpen e.1 omega) := by
  let G := fkIsingSquareCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareMedialCarrier n := .dart (e, .west)
  let N : FKIsingSquareMedialCarrier n := .dart (e, .north)
  let E : FKIsingSquareMedialCarrier n := .dart (e, .east)
  let S : FKIsingSquareMedialCarrier n := .dart (e, .south)
  have hsourceWest : ¬ G.Reachable .source W := by
    simpa only [G, fkIsingSquareCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareExplorationFinset_iff] using hwest
  have hsourceEast : ¬ G.Reachable .source E := by
    simpa only [G, fkIsingSquareCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareExplorationFinset_iff] using heast
  have hwestSouth : G.Adj W S := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .west)) (.dart (e, .south))
    apply Or.inl
    exact Or.inl ⟨(e, .west), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have heastNorth : G.Adj E N := by
    change (fkIsingSquareCompletedLoopGraph n hn
      (setClosed e.1 omega)).Adj (.dart (e, .east)) (.dart (e, .north))
    apply Or.inl
    exact Or.inl ⟨(e, .east), rfl, by
      simp [FKIsingMedialDart.localMate]⟩
  have hiff (z : FKIsingSquareMedialCarrier n) :
      (fkIsingSquareCompletedLoopGraph n hn
          (setOpen e.1 omega)).Reachable .source z ↔
        G.Reachable .source z := by
    rw [fkIsingSquareCompletedLoopGraph_setOpen_eq_twoEdgeSwitch]
    exact medialTwoEdgeSwitch_reachable_iff_of_disjoint G
      hwestSouth heastNorth hsourceWest hsourceEast
  intro side hopen
  have hopenReach :
      (fkIsingSquareCompletedLoopGraph n hn
        (setOpen e.1 omega)).Reachable .source (.dart (e, side)) := by
    rw [fkIsingSquareCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareExplorationFinset_iff]
    exact hopen
  have hclosed : (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) := by
    rw [mem_fkIsingSquareExplorationFinset_iff,
      ← fkIsingSquareCompletedLoopGraph_reachable_source_iff]
    exact (hiff _).1 hopenReach
  cases side
  · exact hwest hclosed
  · exact heast hclosed
  · apply hwest
    rw [mem_fkIsingSquareExplorationFinset_iff]
    have hadj := (fkIsingSquareLoopGraph_adj_dart_iff n hn
      (setClosed e.1 omega) (e, .south) (.dart (e, .west))).2
      (Or.inl (by simp [FKIsingMedialDart.localMate]))
    exact ((mem_fkIsingSquareExplorationFinset_iff _ _ _ _).1 hclosed).trans
      hadj.reachable
  · apply heast
    rw [mem_fkIsingSquareExplorationFinset_iff]
    have hadj := (fkIsingSquareLoopGraph_adj_dart_iff n hn
      (setClosed e.1 omega) (e, .north) (.dart (e, .east))).2
      (Or.inl (by simp [FKIsingMedialDart.localMate]))
    exact ((mem_fkIsingSquareExplorationFinset_iff _ _ _ _).1 hclosed).trans
      hadj.reachable


theorem fkIsingSquare_local_switch_component_classification
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    ((.dart (e, .west) : FKIsingSquareMedialCarrier n) ∉
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∉
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∉
        fkIsingSquareExplorationFinset n hn (setOpen e.1 omega)) ∨
    ((.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∉
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setOpen e.1 omega)) ∨
    ((.dart (e, .west) : FKIsingSquareMedialCarrier n) ∉
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      ∀ side, (.dart (e, side) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setOpen e.1 omega)) ∨
    ((.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)) := by
  classical
  by_cases hwest : (.dart (e, .west) : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)
  · by_cases heast : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)
    · exact Or.inr (Or.inr (Or.inr ⟨hwest, heast⟩))
    · exact Or.inr (Or.inl ⟨hwest, heast,
        fkIsingSquare_open_local_mem_of_closed_west_mem_not_east
          n hn omega e hwest heast⟩)
  · by_cases heast : (.dart (e, .east) : FKIsingSquareMedialCarrier n) ∈
        fkIsingSquareExplorationFinset n hn (setClosed e.1 omega)
    · exact Or.inr (Or.inr (Or.inl ⟨hwest, heast,
        fkIsingSquare_open_local_mem_of_closed_east_mem_not_west
          n hn omega e heast hwest⟩))
    · exact Or.inl ⟨hwest, heast,
        fkIsingSquare_open_local_not_mem_of_closed_west_east_not_mem
          n hn omega e hwest heast⟩

theorem fkIsingSquare_source_mem_exploration (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (.source : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn omega := by
  rw [mem_fkIsingSquareExplorationFinset_iff]

theorem fkIsingSquare_terminal_mem_exploration (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (.terminal : FKIsingSquareMedialCarrier n) ∈
      fkIsingSquareExplorationFinset n hn omega := by
  rw [mem_fkIsingSquareExplorationFinset_iff]
  exact fkIsingSquareLoopGraph_source_reachable_terminal n hn omega


end
end StatMech.Universality
