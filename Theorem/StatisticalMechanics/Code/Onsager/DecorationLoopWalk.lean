/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_walk_count_incident_edges
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (x : V) :
    p.edges.countP (fun edge ↦ x ∈ edge) =
      p.support.dropLast.count x + p.support.tail.count x := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
      rw [SimpleGraph.Walk.edges_cons,
        SimpleGraph.Walk.support_cons]
      simp only [List.countP_cons, List.tail_cons]
      rw [ih]
      rw [← p.cons_tail_support]
      simp only [List.dropLast_cons_cons, List.count_cons,
        List.tail_cons]
      have huvne : u ≠ v := huv.ne
      have hvune : v ≠ u := huv.ne.symm
      simp only [Sym2.mem_iff]
      by_cases hxu : x = u
      · subst x
        simp [huvne, hvune]
        omega
      · by_cases hxv : x = v
        · subst x
          simp [huvne, hvune]
          omega
        · have hux : u ≠ x := fun h ↦ hxu h.symm
          have hvx : v ≠ x := fun h ↦ hxv h.symm
          simp [hxu, hxv, hux, hvx]

theorem ons_closed_walk_count_incident_edges
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u : V} (p : G.Walk u u) (x : V) :
    p.edges.countP (fun edge ↦ x ∈ edge) =
      2 * p.support.tail.count x := by
  rw [ons_walk_count_incident_edges]
  have hsupport :
      p.support.dropLast ++ [u] = u :: p.support.tail :=
    (p.dropLast_support_concat).trans p.cons_tail_support.symm
  have hcount := congrArg (List.count x) hsupport
  simp only [List.count_append, List.count_cons, List.count_nil,
    Nat.add_zero] at hcount
  omega

theorem ons_trail_count_incident_edges_le_degree
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) (x : V) :
    p.edges.countP (fun edge ↦ x ∈ edge) ≤ G.degree x := by
  let F := p.edges.toFinset
  have hFsub : F ⊆ G.edgeFinset := by
    intro edge hedge
    rw [SimpleGraph.mem_edgeFinset]
    exact p.edges_subset_edgeSet (List.mem_toFinset.mp hedge)
  have hcount :
      p.edges.countP (fun edge ↦ x ∈ edge) =
        StatMech.Ising.incCount F x := by
    calc
      p.edges.countP (fun edge ↦ x ∈ edge) =
          (p.edges.filter (fun edge ↦ x ∈ edge)).length :=
        List.countP_eq_length_filter
      _ = (p.edges.filter (fun edge ↦ x ∈ edge)).toFinset.card :=
        (List.toFinset_card_of_nodup
          (hp.edges_nodup.filter (fun edge ↦ x ∈ edge))).symm
      _ = StatMech.Ising.incCount F x := by
        unfold StatMech.Ising.incCount F
        congr 1
        ext edge
        simp
  rw [hcount]
  exact incCount_le_degree G F hFsub x

theorem ons_closed_trail_isCycle_of_degree_le_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {u : V} (p : G.Walk u u) (hp : p.IsTrail)
    (hne : p ≠ .nil) (hdeg : ∀ v, G.degree v ≤ 3) :
    p.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨hp, hne, List.nodup_iff_count_le_one.mpr ?_⟩
  intro x
  have hcount := ons_closed_walk_count_incident_edges p x
  have hle := ons_trail_count_incident_edges_le_degree G hp x
  have hdegree := hdeg x
  omega

theorem ons_decWalkExternalDarts_append
    {L : ℕ} {u v w : ons_Dart L}
    (p : (ons_decGraph L).Walk u v)
    (q : (ons_decGraph L).Walk v w) :
    ons_decWalkExternalDarts (p.append q) =
      ons_decWalkExternalDarts p ++ ons_decWalkExternalDarts q := by
  unfold ons_decWalkExternalDarts
  rw [SimpleGraph.Walk.darts_append, List.filter_append,
    List.map_append]

theorem ons_decPortChainPath_externalDarts_eq_nil
    (L : ℕ) [Fact (2 < L)] (site : ZMod L × ZMod L)
    (a b : Fin 4) :
    ons_decWalkExternalDarts (ons_decPortChainPath L site a b) = [] := by
  unfold ons_decWalkExternalDarts
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro dart hdart hdartExt
  have hedge : dart.edge ∈
      (ons_decPortChainPath L site a b).edges.toFinset := by
    rw [List.mem_toFinset]
    unfold SimpleGraph.Walk.edges
    exact List.mem_map.mpr ⟨dart, hdart, rfl⟩
  rw [ons_decPortChainPath_edges_toFinset] at hedge
  have hrev : dart.snd = ons_dartRev L dart.fst := by
    simpa [ons_decDartIsExternal] using hdartExt
  change s(dart.fst, dart.snd) ∈ ons_decChainPathEdges site a b at hedge
  rw [hrev] at hedge
  exact ons_externalEdge_not_mem_chainPath L dart.fst site a b hedge

theorem ons_decTransitionWalk_externalDarts
    (L : ℕ) [Fact (2 < L)] (d₂ d₁ : ons_Dart L)
    (hstep : d₂.1 = ons_dirStep L d₁.2 d₁.1) :
    ons_decWalkExternalDarts (ons_decTransitionWalk L d₂ d₁ hstep) = [d₁] := by
  have hstart : (d₂.1, d₁.2 + 2) = ons_dartRev L d₁ := by
    apply Prod.ext
    · exact hstep.trans (ons_dartRev_fst_eq_step L d₁).symm
    · simp [ons_dartRev]
  simp only [ons_decTransitionWalk, ons_decWalkExternalDarts_append]
  rw [ons_decWalkExternalDarts_cons_external]
  · simp only [ons_decWalkExternalDarts, SimpleGraph.Walk.darts_nil,
      List.filter_nil, List.map_nil, List.cons_append, List.nil_append,
      List.cons.injEq, true_and]
    rw [List.map_eq_nil_iff]
    rw [SimpleGraph.Walk.darts_copy, List.filter_eq_nil_iff]
    intro dart hdart hdartExt
    have hnil := ons_decPortChainPath_externalDarts_eq_nil
      L d₂.1 (d₁.2 + 2) d₂.2
    unfold ons_decWalkExternalDarts at hnil
    rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at hnil
    exact hnil dart hdart hdartExt
  · rfl

end StatMech.Onsager
