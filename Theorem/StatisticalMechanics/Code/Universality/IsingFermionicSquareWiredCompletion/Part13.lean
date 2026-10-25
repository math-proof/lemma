/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part13


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareWiredWalkCast_support
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWiredWalkCast h p).support = p.support := by
  subst H
  rfl

@[simp] theorem fkIsingSquareWiredWalkCast_isPath
    {V : Type*} {G H : SimpleGraph V} (h : G = H)
    {u v : V} (p : G.Walk u v) :
    (fkIsingSquareWiredWalkCast h p).IsPath ↔ p.IsPath := by
  subst H
  rfl

theorem fkIsingSquareWired_sourceTerminalPath_unique
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (p q : (fkIsingSquareWiredLoopGraph n hn omega).Walk
      (.source : FKIsingSquareWiredCarrier n) .terminal)
    (hp : p.IsPath) (hq : q.IsPath) : p = q := by
  let H := fkIsingSquareWiredLoopGraph n hn omega
  let G := fkIsingSquareWiredCompletedLoopGraph n hn omega
  have hle : H ≤ G := le_sup_left
  have hmem (z : FKIsingSquareWiredCarrier n) :
      z ∈ p.support ↔ z ∈ q.support := by
    rw [fkIsingSquareWiredPath_mem_support_iff_reachable n hn omega p hp,
      fkIsingSquareWiredPath_mem_support_iff_reachable n hn omega q hq]
  have hfin : p.support.toFinset = q.support.toFinset := by
    ext z
    simpa only [List.mem_toFinset] using hmem z
  have hsupportLen : p.support.length = q.support.length := by
    rw [← List.toFinset_card_of_nodup hp.support_nodup,
      ← List.toFinset_card_of_nodup hq.support_nodup, hfin]
  have hlen : p.length = q.length := by
    have hpLengthSupport := p.length_support
    have hqLengthSupport := q.length_support
    omega
  have hcycles : G.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
    simpa only [G] using
      fkIsingSquareWiredCompletedLoopGraph_degree_eq_two n hn omega v
  have hget : ∀ i, i ≤ p.length → p.getVert i = q.getVert i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      by_cases hi0 : i = 0
      · subst i
        simp
      by_cases hi1 : i = 1
      · subst i
        have hpLen : 0 < p.length := by
          by_contra hzero
          have hz : p.length = 0 := Nat.eq_zero_of_not_pos hzero
          have heq := Walk.eq_of_length_eq_zero hz
          simp at heq
        have hqLen : 0 < q.length := by simpa [hlen] using hpLen
        have hpAdj := p.adj_getVert_succ hpLen
        have hqAdj := q.adj_getVert_succ hqLen
        simp only [Walk.getVert_zero, zero_add] at hpAdj hqAdj
        rw [fkIsingSquareWiredLoopGraph_adj_source_iff] at hpAdj hqAdj
        exact hpAdj.trans hqAdj.symm
      have hi2 : 2 ≤ i := by omega
      have him1 : i - 1 < i := by omega
      have him2 : i - 2 < i := by omega
      have hprev := ih (i - 2) him2 (by omega)
      have hcurr := ih (i - 1) him1 (by omega)
      have hpPrevAdj : G.Adj (p.getVert (i - 1)) (p.getVert (i - 2)) := by
        have h := p.adj_getVert_succ (show i - 2 < p.length by omega)
        have heq : i - 2 + 1 = i - 1 := by omega
        rw [heq] at h
        exact (hle h).symm
      obtain ⟨z, _hz, huniq⟩ := hcycles.existsUnique_ne_adj hpPrevAdj
      have hpNext : p.getVert (i - 2) ≠ p.getVert i ∧
          G.Adj (p.getVert (i - 1)) (p.getVert i) := by
        constructor
        · intro heq
          have hinj := hp.getVert_injOn (show i - 2 ≤ p.length by omega)
            hi heq
          omega
        · have h := p.adj_getVert_succ (show i - 1 < p.length by omega)
          have heq : i - 1 + 1 = i := by omega
          rw [heq] at h
          exact hle h
      have hqNext : q.getVert (i - 2) ≠ q.getVert i ∧
          G.Adj (q.getVert (i - 1)) (q.getVert i) := by
        constructor
        · intro heq
          have hinj := hq.getVert_injOn
            (show i - 2 ≤ q.length by omega)
            (show i ≤ q.length by omega) heq
          omega
        · have h := q.adj_getVert_succ (show i - 1 < q.length by omega)
          have heq : i - 1 + 1 = i := by omega
          rw [heq] at h
          exact hle h
      have hpz : p.getVert i = z := huniq _ hpNext
      have hqz : q.getVert i = z := by
        apply huniq
        simpa only [hprev, hcurr] using hqNext
      exact hpz.trans hqz.symm
  apply Walk.ext_support
  apply List.ext_getElem hsupportLen
  intro i hip hiq
  have hpLengthSupport := p.length_support
  have hqLengthSupport := q.length_support
  have hipLength : i ≤ p.length := by omega
  have hiqLength : i ≤ q.length := by omega
  rw [← p.getVert_eq_support_getElem hipLength,
    ← q.getVert_eq_support_getElem hiqLength]
  exact hget i hipLength

theorem fkIsingSquareWiredExplorationPath_mem_edges_of_adj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hx : x ∈ fkIsingSquareWiredExplorationOrder n hn omega)
    (hadj : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
    s(x, y) ∈ (fkIsingSquareWiredExplorationPath n hn omega :
      (fkIsingSquareWiredLoopGraph n hn omega).Walk .source .terminal).edges := by
  let H := fkIsingSquareWiredLoopGraph n hn omega
  let G := fkIsingSquareWiredCompletedLoopGraph n hn omega
  let p : H.Walk (.source : FKIsingSquareWiredCarrier n) .terminal :=
    fkIsingSquareWiredExplorationPath n hn omega
  have hle : H ≤ G := le_sup_left
  have hts : G.Adj (.terminal : FKIsingSquareWiredCarrier n) .source :=
    Or.inr (by simp [SimpleGraph.edge_adj])
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
    exact ⟨(fkIsingSquareWiredExplorationPath n hn omega).isPath.mapLe hle,
      by simpa only [Walk.edges_mapLe_eq_edges] using hedge⟩
  have hcycles : G.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
      SimpleGraph.card_neighborSet_eq_degree]
    simpa only [G] using
      fkIsingSquareWiredCompletedLoopGraph_degree_eq_two n hn omega v
  have hxq : x ∈ q.toSubgraph.verts := by
    rw [Walk.mem_verts_toSubgraph]
    simp only [q, Walk.support_cons, List.mem_cons,
      Walk.support_mapLe_eq_support]
    right
    simpa [p, fkIsingSquareWiredExplorationOrder] using hx
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
