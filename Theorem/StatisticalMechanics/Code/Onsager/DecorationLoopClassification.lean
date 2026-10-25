/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part7


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_isPath_eq_of_edges_toFinset_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (p q : G.Walk u v) (hp : p.IsPath) (hq : q.IsPath)
    (hedges : p.edges.toFinset = q.edges.toFinset) :
    p = q := by
  induction p with
  | nil =>
      have hqEmpty : q.edges.toFinset = ∅ := by
        simpa using hedges.symm
      have hqEdges : q.edges = [] :=
        (List.toFinset_eq_empty_iff q.edges).mp hqEmpty
      have hqnil : q.Nil := SimpleGraph.Walk.edges_eq_nil.mp hqEdges
      exact hqnil.eq_nil.symm
  | @cons u w v huw p ih =>
      cases q with
      | nil =>
          have hedge : s(u, w) ∈
              (SimpleGraph.Walk.cons huw p).edges.toFinset := by simp
          rw [hedges] at hedge
          simpa using hedge
      | @cons _ w' _ huw' q =>
          have hedgeP : s(u, w) ∈
              (SimpleGraph.Walk.cons huw p).edges.toFinset := by simp
          have hedgeQ : s(u, w) ∈
              (SimpleGraph.Walk.cons huw' q).edges := by
            exact List.mem_toFinset.mp (hedges ▸ hedgeP)
          have hw : w' = w := by
            have hsnd := hq.eq_snd_of_mem_edges hedgeQ
            simpa using hsnd.symm
          subst w'
          have hpTail : p.IsPath := by
            simpa using hp.tail
          have hqTail : q.IsPath := by
            simpa using hq.tail
          have hpnList : s(u, w) ∉ p.edges := by
            have hnodup := hp.isTrail.edges_nodup
            rw [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
            exact hnodup.1
          have hqnList : s(u, w) ∉ q.edges := by
            have hnodup := hq.isTrail.edges_nodup
            rw [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
            exact hnodup.1
          have htailEdges : p.edges.toFinset = q.edges.toFinset := by
            have herase := congrArg
              (Finset.erase · s(u, w)) hedges
            simp only [SimpleGraph.Walk.edges_cons,
              List.toFinset_cons] at herase
            rw [Finset.erase_insert
                (mt List.mem_toFinset.mp hpnList),
              Finset.erase_insert
                (mt List.mem_toFinset.mp hqnList)] at herase
            exact herase
          have hpq : p = q := ih q hpTail hqTail htailEdges
          subst q
          rfl

theorem ons_rooted_isCycle_eq_of_snd_edges_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u : V}
    (p q : G.Walk u u) (hp : p.IsCycle) (hq : q.IsCycle)
    (hsnd : p.snd = q.snd)
    (hedges : p.edges.toFinset = q.edges.toFinset) :
    p = q := by
  have hpne : ¬p.Nil := hp.not_nil
  have hqne : ¬q.Nil := hq.not_nil
  let edge : Sym2 V := s(u, p.snd)
  let qtail : G.Walk p.snd u := q.tail.copy hsnd.symm rfl
  have hpNot : edge ∉ p.tail.edges := by
    have hnodup := hp.edges_nodup
    rw [← p.cons_tail_eq hpne,
      SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
    exact hnodup.1
  have hqNot : edge ∉ q.tail.edges := by
    have hnodup := hq.edges_nodup
    rw [← q.cons_tail_eq hqne,
      SimpleGraph.Walk.edges_cons, List.nodup_cons] at hnodup
    simpa [edge, hsnd] using hnodup.1
  have htailEdges : p.tail.edges.toFinset = qtail.edges.toFinset := by
    have hedges' := hedges
    rw [← p.cons_tail_eq hpne, ← q.cons_tail_eq hqne,
      SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_cons,
      List.toFinset_cons, List.toFinset_cons] at hedges'
    have hedgeSnd : s(u, q.snd) = edge := by
      rw [← hsnd]
    rw [hedgeSnd] at hedges'
    change insert edge p.tail.edges.toFinset =
      insert edge q.tail.edges.toFinset at hedges'
    have herase := congrArg (Finset.erase · edge) hedges'
    change (insert edge p.tail.edges.toFinset).erase edge =
      (insert edge q.tail.edges.toFinset).erase edge at herase
    rw [Finset.erase_insert (mt List.mem_toFinset.mp hpNot),
      Finset.erase_insert (mt List.mem_toFinset.mp hqNot)] at herase
    simpa [qtail, SimpleGraph.Walk.edges_copy] using herase
  have hqtailPath : qtail.IsPath := by
    exact (SimpleGraph.Walk.isPath_copy q.tail hsnd.symm rfl).mpr
      hq.isPath_tail
  have htail : p.tail = qtail :=
    ons_isPath_eq_of_edges_toFinset_eq p.tail qtail
      hp.isPath_tail hqtailPath htailEdges
  have htailHEq : p.tail ≍ q.tail := by
    apply (heq_of_eq htail).trans
    simp [qtail, SimpleGraph.Walk.copy]
  have hcons :
      SimpleGraph.Walk.cons (p.adj_snd hpne) p.tail =
        SimpleGraph.Walk.cons (q.adj_snd hqne) q.tail := by
    rw [SimpleGraph.Walk.cons.injEq]
    exact ⟨hsnd, htailHEq⟩
  calc
    p = SimpleGraph.Walk.cons (p.adj_snd hpne) p.tail :=
      (p.cons_tail_eq hpne).symm
    _ = SimpleGraph.Walk.cons (q.adj_snd hqne) q.tail := hcons
    _ = q := q.cons_tail_eq hqne

theorem ons_decCycleDartList_copy
    {L : ℕ} {d e : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (h : d = e) :
    ons_decCycleDartList (q.copy h h) = ons_decCycleDartList q := by
  subst e
  rfl

theorem ons_squarefree_valid_loop_eq_of_zero_eq
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d e : Fin n → ons_Dart L)
    (hdvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (hevalid : ∀ k : Fin n,
      (e k).1 = ons_dirStep L (e (k + 1)).2 (e (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hdexp : ons_decLoopExponent L d = ons_finsetExponent S)
    (heexp : ons_decLoopExponent L e = ons_finsetExponent S)
    (hzero : d 0 = e 0) :
    d = e := by
  let qd := ons_decLoopWalk L d hdvalid
  let qe := ons_decLoopWalk L e hevalid
  let qe' : (ons_decGraph L).Walk (d 0) (d 0) :=
    qe.copy hzero.symm hzero.symm
  have hqd : qd.IsCycle :=
    ons_decLoopWalk_isCycle_of_squarefree L d hdvalid S hdexp
  have hqe : qe.IsCycle :=
    ons_decLoopWalk_isCycle_of_squarefree L e hevalid S heexp
  have hqe' : qe'.IsCycle := by
    exact (SimpleGraph.Walk.isCycle_copy qe hzero.symm).mpr hqe
  have hsnd : qd.snd = qe'.snd := by
    change qd.getVert 1 = qe'.getVert 1
    rw [show qd.getVert 1 = qd.snd from rfl,
      show qe'.getVert 1 = qe'.snd from rfl,
      ons_decLoopWalk_snd L d hdvalid]
    change ons_dartRev L (d 0) = (qe.copy hzero.symm hzero.symm).getVert 1
    rw [SimpleGraph.Walk.getVert_copy]
    change ons_dartRev L (d 0) = qe.snd
    rw [ons_decLoopWalk_snd L e hevalid, hzero]
  have hedges : qd.edges.toFinset = qe'.edges.toFinset := by
    rw [show qd.edges.toFinset = S from
      ons_decLoopWalk_edges_toFinset_of_squarefree
        L d hdvalid S hdexp]
    rw [SimpleGraph.Walk.edges_copy]
    exact (ons_decLoopWalk_edges_toFinset_of_squarefree
      L e hevalid S heexp).symm
  have hq : qd = qe' :=
    ons_rooted_isCycle_eq_of_snd_edges_eq qd qe' hqd hqe' hsnd hedges
  apply List.ofFn_injective
  rw [← ons_decLoopWalk_cycleDartList L d hdvalid,
    ← ons_decLoopWalk_cycleDartList L e hevalid]
  calc
    ons_decCycleDartList qd = ons_decCycleDartList qe' :=
      congrArg ons_decCycleDartList hq
    _ = ons_decCycleDartList qe :=
      ons_decCycleDartList_copy qe hzero.symm

end StatMech.Onsager
