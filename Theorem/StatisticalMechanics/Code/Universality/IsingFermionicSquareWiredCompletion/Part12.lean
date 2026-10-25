/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable .source z ↔
      (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z := by
  rw [fkIsingSquareWiredCompletedLoopGraph, reachable_sup_edge_iff]
  constructor
  · rintro (h | ⟨_, hterminal⟩ | ⟨_, hsource⟩)
    · exact h
    · exact (fkIsingSquareWiredLoopGraph_source_reachable_terminal
        n hn omega).trans hterminal
    · exact hsource
  · exact Or.inl

theorem fkIsingSquareWiredCompletedLoopGraph_source_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).degree .source = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).neighborFinset .source =
        {.bond (fkIsingSquareWiredSourceDart n hn), .terminal} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareWiredCompletedLoopGraph, SimpleGraph.edge_adj]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, by simp⟩
  rw [hfin]
  simp

theorem fkIsingSquareWiredCompletedLoopGraph_terminal_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).degree .terminal = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).neighborFinset .terminal =
        {.bond (fkIsingSquareWiredTerminalDart n hn), .source} := by
    ext z
    rw [SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareWiredCompletedLoopGraph, SimpleGraph.edge_adj]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, by simp⟩
  rw [hfin]
  simp

theorem fkIsingSquareWiredCompletedLoopGraph_internal_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n)
    (hsource : x ≠ .source) (hterminal : x ≠ .terminal) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).degree x = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hfin :
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).neighborFinset x =
        (fkIsingSquareWiredLoopGraph n hn omega).neighborFinset x := by
    ext z
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
    simp [fkIsingSquareWiredCompletedLoopGraph, SimpleGraph.edge_adj,
      hsource, hterminal]
  rw [hfin, SimpleGraph.card_neighborFinset_eq_degree,
    fkIsingSquareWiredLoopGraph_internal_degree n hn omega x
      hsource hterminal]

theorem fkIsingSquareWiredCompletedLoopGraph_even_degree
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    Even ((fkIsingSquareWiredCompletedLoopGraph n hn omega).degree x) := by
  by_cases hs : x = .source
  · subst x
    rw [fkIsingSquareWiredCompletedLoopGraph_source_degree]
    exact even_two
  by_cases ht : x = .terminal
  · subst x
    rw [fkIsingSquareWiredCompletedLoopGraph_terminal_degree]
    exact even_two
  · rw [fkIsingSquareWiredCompletedLoopGraph_internal_degree
      n hn omega x hs ht]
    exact even_two

theorem fkIsingSquareWiredCompletedLoopGraph_degree_eq_two
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x : FKIsingSquareWiredCarrier n) :
    (fkIsingSquareWiredCompletedLoopGraph n hn omega).degree x = 2 := by
  by_cases hs : x = .source
  · subst x
    exact fkIsingSquareWiredCompletedLoopGraph_source_degree n hn omega
  by_cases ht : x = .terminal
  · subst x
    exact fkIsingSquareWiredCompletedLoopGraph_terminal_degree n hn omega
  · exact fkIsingSquareWiredCompletedLoopGraph_internal_degree
      n hn omega x hs ht

set_option maxHeartbeats 1000000 in
theorem fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredCompletedLoopGraph n hn (setOpen e.1 omega) =
      medialTwoEdgeSwitch
        (fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega))
        (.dart (e, .west)) (.dart (e, .south))
        (.dart (e, .east)) (.dart (e, .north)) := by
  rw [fkIsingSquareWiredCompletedLoopGraph,
    fkIsingSquareWiredLoopGraph_setOpen_eq_twoEdgeSwitch]
  ext x y
  cases x <;> cases y <;>
    simp [fkIsingSquareWiredCompletedLoopGraph, medialTwoEdgeSwitch,
      SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
      SimpleGraph.edge_adj]

theorem fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)).Adj
      (.dart (e, .west)) (.dart (e, .south)) := by
  apply Or.inl
  exact Or.inr (by simp [fkIsingSquareWiredTransitionMate,
    FKIsingMedialDart.localMate])

theorem fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)).Adj
      (.dart (e, .east)) (.dart (e, .north)) := by
  apply Or.inl
  exact Or.inr (by simp [fkIsingSquareWiredTransitionMate,
    FKIsingMedialDart.localMate])

theorem fkIsingSquareWired_open_local_mem_of_closed_west_mem_not_east
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega))
    (heast : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∉
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)) :
    ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
  let G := fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  have hsourceWest : G.Reachable .source W := by
    change (fkIsingSquareWiredCompletedLoopGraph n hn
      (setClosed e.1 omega)).Reachable .source (.dart (e, .west))
    rw [fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareWiredExplorationTrace_iff]
    exact hwest
  have hwestEast : ¬ G.Reachable W E := by
    intro h
    apply heast
    rw [mem_fkIsingSquareWiredExplorationTrace_iff,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    exact hsourceWest.trans h
  have hwestSouth : G.Adj W S :=
    fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj
      n hn omega e
  have heastNorth : G.Adj E N :=
    fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj
      n hn omega e
  have hall := medialTwoEdgeSwitch_reachable_all_of_reachable_left G
    (fkIsingSquareWiredCompletedLoopGraph_even_degree n hn
      (setClosed e.1 omega))
    hwestSouth heastNorth hwestEast hsourceWest
  rw [← fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    n hn omega e] at hall
  intro side
  rw [mem_fkIsingSquareWiredExplorationTrace_iff,
    ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
  cases side
  · exact hall.1
  · exact hall.2.2.1
  · exact hall.2.1
  · exact hall.2.2.2

theorem fkIsingSquareWired_open_local_mem_of_closed_east_mem_not_west
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (heast : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega))
    (hwest : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∉
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)) :
    ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
  let G := fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  have hsourceEast : G.Reachable .source E := by
    change (fkIsingSquareWiredCompletedLoopGraph n hn
      (setClosed e.1 omega)).Reachable .source (.dart (e, .east))
    rw [fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareWiredExplorationTrace_iff]
    exact heast
  have hwestEast : ¬ G.Reachable W E := by
    intro h
    apply hwest
    rw [mem_fkIsingSquareWiredExplorationTrace_iff,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    exact hsourceEast.trans h.symm
  have hwestSouth : G.Adj W S :=
    fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj
      n hn omega e
  have heastNorth : G.Adj E N :=
    fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj
      n hn omega e
  have hall := medialTwoEdgeSwitch_reachable_all_of_reachable_right G
    (fkIsingSquareWiredCompletedLoopGraph_even_degree n hn
      (setClosed e.1 omega))
    hwestSouth heastNorth hwestEast hsourceEast
  rw [← fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch
    n hn omega e] at hall
  intro side
  rw [mem_fkIsingSquareWiredExplorationTrace_iff,
    ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
  cases side
  · exact hall.1
  · exact hall.2.2.1
  · exact hall.2.1
  · exact hall.2.2.2

theorem fkIsingSquareWired_open_local_not_mem_of_closed_west_east_not_mem
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hwest : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∉
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega))
    (heast : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∉
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)) :
    ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
      fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega) := by
  let G := fkIsingSquareWiredCompletedLoopGraph n hn (setClosed e.1 omega)
  let W : FKIsingSquareWiredCarrier n := .dart (e, .west)
  let N : FKIsingSquareWiredCarrier n := .dart (e, .north)
  let E : FKIsingSquareWiredCarrier n := .dart (e, .east)
  let S : FKIsingSquareWiredCarrier n := .dart (e, .south)
  have hsourceWest : ¬ G.Reachable .source W := by
    simpa only [G, fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareWiredExplorationTrace_iff] using hwest
  have hsourceEast : ¬ G.Reachable .source E := by
    simpa only [G, fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareWiredExplorationTrace_iff] using heast
  have hwestSouth : G.Adj W S :=
    fkIsingSquareWiredCompletedLoopGraph_closed_west_south_adj
      n hn omega e
  have heastNorth : G.Adj E N :=
    fkIsingSquareWiredCompletedLoopGraph_closed_east_north_adj
      n hn omega e
  have hiff (z : FKIsingSquareWiredCarrier n) :
      (fkIsingSquareWiredCompletedLoopGraph n hn
          (setOpen e.1 omega)).Reachable .source z ↔
        G.Reachable .source z := by
    rw [fkIsingSquareWiredCompletedLoopGraph_setOpen_eq_twoEdgeSwitch]
    exact medialTwoEdgeSwitch_reachable_iff_of_disjoint G
      hwestSouth heastNorth hsourceWest hsourceEast
  intro side hopen
  have hopenReach :
      (fkIsingSquareWiredCompletedLoopGraph n hn
        (setOpen e.1 omega)).Reachable .source (.dart (e, side)) := by
    rw [fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff,
      ← mem_fkIsingSquareWiredExplorationTrace_iff]
    exact hopen
  have hclosed : (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) := by
    rw [mem_fkIsingSquareWiredExplorationTrace_iff,
      ← fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
    exact (hiff _).1 hopenReach
  cases side
  · exact hwest hclosed
  · exact heast hclosed
  · exact hwest
      ((fkIsingSquareWired_closed_west_mem_iff_south n hn omega e).2 hclosed)
  · exact heast
      ((fkIsingSquareWired_closed_east_mem_iff_north n hn omega e).2 hclosed)


theorem fkIsingSquareWired_local_switch_component_classification
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    ((.dart (e, .west) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega)) ∨
    ((.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega)) ∨
    ((.dart (e, .west) : FKIsingSquareWiredCarrier n) ∉
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setOpen e.1 omega)) ∨
    ((.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega) ∧
      (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)) := by
  classical
  by_cases hwest : (.dart (e, .west) : FKIsingSquareWiredCarrier n) ∈
      fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)
  · by_cases heast : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)
    · exact Or.inr (Or.inr (Or.inr ⟨hwest, heast⟩))
    · exact Or.inr (Or.inl ⟨hwest, heast,
        fkIsingSquareWired_open_local_mem_of_closed_west_mem_not_east
          n hn omega e hwest heast⟩)
  · by_cases heast : (.dart (e, .east) : FKIsingSquareWiredCarrier n) ∈
        fkIsingSquareWiredExplorationTrace n hn (setClosed e.1 omega)
    · exact Or.inr (Or.inr (Or.inl ⟨hwest, heast,
        fkIsingSquareWired_open_local_mem_of_closed_east_mem_not_west
          n hn omega e heast hwest⟩))
    · exact Or.inl ⟨hwest, heast,
        fkIsingSquareWired_open_local_not_mem_of_closed_west_east_not_mem
          n hn omega e hwest heast⟩


theorem fkIsingSquareWiredPath_mem_support_iff_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (p : (fkIsingSquareWiredLoopGraph n hn omega).Walk
      (.source : FKIsingSquareWiredCarrier n) .terminal)
    (hp : p.IsPath) (z : FKIsingSquareWiredCarrier n) :
    z ∈ p.support ↔
      (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z := by
  let H := fkIsingSquareWiredLoopGraph n hn omega
  let G := fkIsingSquareWiredCompletedLoopGraph n hn omega
  have hle : H ≤ G := le_sup_left
  have hts : G.Adj (.terminal : FKIsingSquareWiredCarrier n) .source := by
    exact Or.inr (by simp [SimpleGraph.edge_adj])
  have hst_not_adj :
      ¬ H.Adj (.terminal : FKIsingSquareWiredCarrier n) .source := by
    intro h
    have h' := h.symm
    rw [fkIsingSquareWiredLoopGraph_adj_source_iff] at h'
    simp at h'
  have hedge :
      s((.terminal : FKIsingSquareWiredCarrier n), .source) ∉ p.edges := by
    intro h
    exact hst_not_adj (p.adj_of_mem_edges h)
  let q : G.Walk (.terminal : FKIsingSquareWiredCarrier n) .terminal :=
    (p.mapLe hle).cons hts
  have hq : q.IsCycle := by
    change ((p.mapLe hle).cons hts).IsCycle
    rw [Walk.cons_isCycle_iff]
    exact ⟨hp.mapLe hle,
      by simpa only [Walk.edges_mapLe_eq_edges] using hedge⟩
  have hcycles : G.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
    cases v with
    | source =>
        simpa only [G] using
          fkIsingSquareWiredCompletedLoopGraph_source_degree n hn omega
    | terminal =>
        simpa only [G] using
          fkIsingSquareWiredCompletedLoopGraph_terminal_degree n hn omega
    | dart d =>
        simpa only [G] using
          fkIsingSquareWiredCompletedLoopGraph_internal_degree
            n hn omega (.dart d) (by simp) (by simp)
    | bond d =>
        simpa only [G] using
          fkIsingSquareWiredCompletedLoopGraph_internal_degree
            n hn omega (.bond d) (by simp) (by simp)
  constructor
  · intro hz
    exact (p.takeUntil z hz).reachable
  · intro hz
    have hclosed : ∀ v, v ∈ q.toSubgraph.verts →
        ∀ w, G.Adj v w → q.toSubgraph.Adj v w := by
      intro v hv w hadj
      exact (hq.adj_toSubgraph_iff_of_isCycles hcycles hv w).2 hadj
    obtain ⟨c, hc⟩ :=
      q.toSubgraph_connected.exists_verts_eq_connectedComponentSupp hclosed
    have hsource : (.source : FKIsingSquareWiredCarrier n) ∈ c.supp := by
      rw [← hc, Walk.mem_verts_toSubgraph]
      simp [q]
    have hzG : G.Reachable .source z := by
      rw [fkIsingSquareWiredCompletedLoopGraph_reachable_source_iff]
      exact hz
    have hzc : z ∈ c.supp := by
      rw [c.mem_supp_iff]
      exact hsource ▸ ConnectedComponent.sound hzG.symm
    rw [← hc, Walk.mem_verts_toSubgraph] at hzc
    simp only [q, Walk.support_cons, List.mem_cons] at hzc
    rcases hzc with rfl | hzc
    · simp
    · simpa only [Walk.support_mapLe_eq_support] using hzc

theorem mem_fkIsingSquareWiredExplorationOrder_iff_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    z ∈ fkIsingSquareWiredExplorationOrder n hn omega ↔
      (fkIsingSquareWiredLoopGraph n hn omega).Reachable .source z := by
  simpa only [fkIsingSquareWiredExplorationOrder] using
    fkIsingSquareWiredPath_mem_support_iff_reachable n hn omega
      (fkIsingSquareWiredExplorationPath n hn omega)
      (fkIsingSquareWiredExplorationPath n hn omega).isPath z

theorem mem_fkIsingSquareWiredExplorationOrder_iff_trace
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareWiredCarrier n) :
    z ∈ fkIsingSquareWiredExplorationOrder n hn omega ↔
      z ∈ fkIsingSquareWiredExplorationTrace n hn omega := by
  rw [mem_fkIsingSquareWiredExplorationOrder_iff_reachable,
    mem_fkIsingSquareWiredExplorationTrace_iff]

end
end StatMech.Universality
