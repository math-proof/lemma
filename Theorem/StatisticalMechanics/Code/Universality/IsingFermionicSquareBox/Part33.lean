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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part30


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareExplorationOrder_nodup (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    (fkIsingSquareExplorationOrder n hn omega).Nodup :=
  (fkIsingSquareExplorationPath n hn omega).isPath.support_nodup

theorem fkIsingSquareExplorationPath_oddClass
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (i : Nat)
    (hi : i ≤ (fkIsingSquareExplorationPath n hn omega :
      (fkIsingSquareLoopGraph n hn omega).Walk .source .terminal).length) :
    fkIsingSquareCarrierOddClass n
        ((fkIsingSquareExplorationPath n hn omega :
          (fkIsingSquareLoopGraph n hn omega).Walk .source .terminal).getVert i) ↔
      Odd i := by
  let p : (fkIsingSquareLoopGraph n hn omega).Walk
      (.source : FKIsingSquareMedialCarrier n) .terminal :=
    fkIsingSquareExplorationPath n hn omega
  change fkIsingSquareCarrierOddClass n (p.getVert i) ↔ Odd i
  induction i with
  | zero =>
      simp [p, fkIsingSquareCarrierOddClass]
  | succ i ih =>
      have hi0 : i < p.length := by simpa [p] using hi
      have hadj := p.adj_getVert_succ hi0
      have hflip := fkIsingSquareLoopGraph_adj_oddClass n hn omega hadj
      have ih' := ih (by simpa [p] using Nat.le_of_lt hi0)
      have hrev : fkIsingSquareCarrierOddClass n (p.getVert (i + 1)) ↔
          ¬ fkIsingSquareCarrierOddClass n (p.getVert i) := by
        tauto
      rw [hrev, ih', Nat.odd_add_one]


theorem fkIsingSquarePath_mem_support_iff_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (p : (fkIsingSquareLoopGraph n hn omega).Walk
      (.source : FKIsingSquareMedialCarrier n) .terminal)
    (hp : p.IsPath)
    (z : FKIsingSquareMedialCarrier n) :
    z ∈ p.support ↔
      (fkIsingSquareLoopGraph n hn omega).Reachable .source z := by
  let H := fkIsingSquareLoopGraph n hn omega
  let G := fkIsingSquareCompletedLoopGraph n hn omega
  have hle : H ≤ G := le_sup_left
  have hts : G.Adj (.terminal : FKIsingSquareMedialCarrier n) .source := by
    exact Or.inr (by simp [SimpleGraph.edge_adj])
  have hst_not_adj :
      ¬ H.Adj (.terminal : FKIsingSquareMedialCarrier n) .source := by
    change ¬(fkIsingSquareLoopGraph n hn omega).Adj
      (.terminal : FKIsingSquareMedialCarrier n) .source
    intro h
    have h' := h.symm
    rw [fkIsingSquareLoopGraph_adj_source_iff] at h'
    simp at h'
  have hedge :
      s((.terminal : FKIsingSquareMedialCarrier n), .source) ∉ p.edges := by
    intro h
    exact hst_not_adj (p.adj_of_mem_edges h)
  let q : G.Walk (.terminal : FKIsingSquareMedialCarrier n) .terminal :=
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
    | source => exact fkIsingSquareCompletedLoopGraph_source_degree n hn omega
    | terminal => exact fkIsingSquareCompletedLoopGraph_terminal_degree n hn omega
    | dart d => exact fkIsingSquareCompletedLoopGraph_dart_degree n hn omega d
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
    have hsource : (.source : FKIsingSquareMedialCarrier n) ∈ c.supp := by
      rw [← hc, Walk.mem_verts_toSubgraph]
      simp [q]
    have hzG : G.Reachable .source z := by
      rw [fkIsingSquareCompletedLoopGraph_reachable_source_iff]
      exact hz
    have hzc : z ∈ c.supp := by
      rw [c.mem_supp_iff]
      exact hsource ▸ ConnectedComponent.sound hzG.symm
    rw [← hc, Walk.mem_verts_toSubgraph] at hzc
    simp only [q, Walk.support_cons, List.mem_cons] at hzc
    rcases hzc with rfl | hzc
    · simp
    · simpa only [Walk.support_mapLe_eq_support] using hzc


theorem mem_fkIsingSquareExplorationOrder_iff_reachable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    z ∈ fkIsingSquareExplorationOrder n hn omega ↔
      (fkIsingSquareLoopGraph n hn omega).Reachable .source z := by
  simpa only [fkIsingSquareExplorationOrder] using
    fkIsingSquarePath_mem_support_iff_reachable n hn omega
      (fkIsingSquareExplorationPath n hn omega)
      (fkIsingSquareExplorationPath n hn omega).isPath z

theorem mem_fkIsingSquareExplorationOrder_iff_finset
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (z : FKIsingSquareMedialCarrier n) :
    z ∈ fkIsingSquareExplorationOrder n hn omega ↔
      z ∈ fkIsingSquareExplorationFinset n hn omega := by
  rw [mem_fkIsingSquareExplorationOrder_iff_reachable,
    mem_fkIsingSquareExplorationFinset_iff]


theorem fkIsingSquareExplorationPath_mem_edges_of_adj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareMedialCarrier n}
    (hx : x ∈ fkIsingSquareExplorationOrder n hn omega)
    (hadj : (fkIsingSquareLoopGraph n hn omega).Adj x y) :
    s(x, y) ∈ (fkIsingSquareExplorationPath n hn omega :
      (fkIsingSquareLoopGraph n hn omega).Walk .source .terminal).edges := by
  let H := fkIsingSquareLoopGraph n hn omega
  let G := fkIsingSquareCompletedLoopGraph n hn omega
  let p : H.Walk (.source : FKIsingSquareMedialCarrier n) .terminal :=
    fkIsingSquareExplorationPath n hn omega
  have hle : H ≤ G := le_sup_left
  have hts : G.Adj (.terminal : FKIsingSquareMedialCarrier n) .source :=
    Or.inr (by simp [SimpleGraph.edge_adj])
  have hst_not_adj :
      ¬ H.Adj (.terminal : FKIsingSquareMedialCarrier n) .source := by
    change ¬(fkIsingSquareLoopGraph n hn omega).Adj
      (.terminal : FKIsingSquareMedialCarrier n) .source
    intro h
    have h' := h.symm
    rw [fkIsingSquareLoopGraph_adj_source_iff] at h'
    simp at h'
  have hedge :
      s((.terminal : FKIsingSquareMedialCarrier n), .source) ∉ p.edges := by
    intro h
    exact hst_not_adj (p.adj_of_mem_edges h)
  let q : G.Walk (.terminal : FKIsingSquareMedialCarrier n) .terminal :=
    (p.mapLe hle).cons hts
  have hq : q.IsCycle := by
    change ((p.mapLe hle).cons hts).IsCycle
    rw [Walk.cons_isCycle_iff]
    exact ⟨(fkIsingSquareExplorationPath n hn omega).isPath.mapLe hle,
      by simpa only [Walk.edges_mapLe_eq_edges] using hedge⟩
  have hcycles : G.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
    cases v with
    | source => exact fkIsingSquareCompletedLoopGraph_source_degree n hn omega
    | terminal => exact fkIsingSquareCompletedLoopGraph_terminal_degree n hn omega
    | dart d => exact fkIsingSquareCompletedLoopGraph_dart_degree n hn omega d
  have hxq : x ∈ q.toSubgraph.verts := by
    rw [Walk.mem_verts_toSubgraph]
    simp only [q, Walk.support_cons, List.mem_cons,
      Walk.support_mapLe_eq_support]
    right
    simpa [p, fkIsingSquareExplorationOrder] using hx
  have hqadj : q.toSubgraph.Adj x y :=
    (hq.adj_toSubgraph_iff_of_isCycles hcycles hxq y).2 (hle hadj)
  rw [Walk.adj_toSubgraph_iff_mem_edges] at hqadj
  simp only [q, Walk.edges_cons, List.mem_cons,
    Walk.edges_mapLe_eq_edges] at hqadj
  rcases hqadj with hxy | hxy
  · rcases Sym2.eq_iff.mp hxy with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact False.elim (hst_not_adj hadj)
    · rcases h with ⟨rfl, rfl⟩
      exact False.elim (hst_not_adj hadj.symm)
  · exact hxy


end
end StatMech.Universality
