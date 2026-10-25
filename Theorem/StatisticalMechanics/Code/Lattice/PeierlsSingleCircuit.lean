/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsSingleCircuit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable


namespace EulerianExistence

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem degree_eq_card_filter_edges (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    G.degree x = (G.edgeFinset.filter (fun e => x ∈ e)).card := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree, SimpleGraph.incidenceFinset_eq_filter]


theorem edgeFinset_deleteEdges_finset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) :
    (G.deleteEdges (S : Set (Sym2 V))).edgeFinset = G.edgeFinset \ S := by
  classical
  have hdec : DecidableRel (G.deleteEdges (S : Set (Sym2 V))).Adj := Classical.decRel _
  apply Finset.coe_injective
  rw [Finset.coe_sdiff, coe_edgeFinset, coe_edgeFinset, SimpleGraph.edgeSet_deleteEdges]


theorem even_degree_deleteEdges_closedTrail (G : SimpleGraph V) [DecidableRel G.Adj]
    {u : V} {p : G.Walk u u} (hp : p.IsTrail) (x : V) (hx : Even (G.degree x)) :
    Even ((G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).degree x) := by
  classical
  have hdec : DecidableRel (G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).Adj :=
    Classical.decRel _
  rw [degree_eq_card_filter_edges, edgeFinset_deleteEdges_finset]
  have hfsd : (G.edgeFinset \ p.edges.toFinset).filter (fun e => x ∈ e)
      = G.edgeFinset.filter (fun e => x ∈ e) \ (p.edges.toFinset).filter (fun e => x ∈ e) := by
    ext e; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
  rw [hfsd]
  set A := G.edgeFinset.filter (fun e => x ∈ e) with hA
  set B := (p.edges.toFinset).filter (fun e => x ∈ e) with hB
  have hAeven : Even A.card := by rw [hA, ← degree_eq_card_filter_edges]; exact hx
  
  have hBA : B ⊆ A := by
    intro e he
    rw [hB, Finset.mem_filter] at he
    rw [hA, Finset.mem_filter]
    exact ⟨(SimpleGraph.mem_edgeFinset).mpr (p.edges_subset_edgeSet (List.mem_toFinset.mp he.1)),
      he.2⟩
  
  have hBeven : Even B.card := by
    have hnd : p.edges.Nodup := hp.edges_nodup
    have hcard : B.card = (p.edges.filter (fun e => decide (x ∈ e))).length := by
      rw [hB]
      have : ({e ∈ p.edges.toFinset | x ∈ e} : Finset (Sym2 V))
          = (p.edges.filter (fun e => decide (x ∈ e))).toFinset := by
        rw [List.toFinset_filter]; apply Finset.filter_congr; intro e _
        simp [decide_eq_true_eq]
      rw [this, List.toFinset_card_of_nodup (hnd.filter _)]
    rw [hcard, ← List.countP_eq_length_filter]
    exact (hp.even_countP_edges_iff x).mpr (fun h => absurd rfl h)
  
  rw [Finset.card_sdiff_of_subset hBA]
  exact (Nat.even_sub (Finset.card_le_card hBA)).mpr (iff_of_true hAeven hBeven)


omit [DecidableEq V] in


theorem exists_maximal_closed_trail (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    ∃ p : G.Walk u u, p.IsTrail ∧
      ∀ q : G.Walk u u, q.IsTrail → q.length ≤ p.length := by
  classical
  
  set P : ℕ → Prop := fun k => ∃ q : G.Walk u u, q.IsTrail ∧ q.length = k with hP
  have hP0 : P 0 := ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsTrail.nil, rfl⟩
  
  have hbound : ∀ k, P k → k ≤ G.edgeFinset.card := by
    rintro k ⟨q, hq, rfl⟩; exact hq.length_le_card_edgeFinset
  
  set N := Nat.findGreatest P G.edgeFinset.card with hN
  have hNP : P N := Nat.findGreatest_spec (Nat.zero_le _) hP0
  obtain ⟨p, hp, hplen⟩ := hNP
  refine ⟨p, hp, ?_⟩
  intro q hq
  have hqlen : q.length ≤ G.edgeFinset.card := hq.length_le_card_edgeFinset
  have hqP : P q.length := ⟨q, hq, rfl⟩
  rw [hplen]
  exact Nat.le_findGreatest hqlen hqP


end EulerianExistence
end Lattice
end StatMech
