/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbeddingDisjoint
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbeddingTurns.Part2


namespace StatMech.Onsager

theorem ons_decExpandedDartList_sum_exponentX
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    ((ons_decExpandedDartList L p).map
      (fun a => ons_dirExponentX a.2)).sum =
        2 * (ons_dirExponentX v.2 - ons_dirExponentX u.2) +
          8 * ((ons_decWalkExternalDarts p).map
            (fun a => ons_dirExponentX a.2)).sum := by
  induction p with
  | nil => simp [ons_decExpandedDartList, ons_decWalkExternalDarts]
  | @cons u w v huw p ih =>
      simp only [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons, List.map_append, List.sum_append]
      have ih' :
          ((List.flatMap
            (fun a => ons_decEdgeMicroDarts L a.fst a.snd) p.darts).map
              (fun a => ons_dirExponentX a.2)).sum =
            2 * (ons_dirExponentX v.2 - ons_dirExponentX w.2) +
              8 * ((ons_decWalkExternalDarts p).map
                (fun a => ons_dirExponentX a.2)).sum := by
        simpa only [ons_decExpandedDartList] using ih
      by_cases hrev : w = ons_dartRev L u
      · rw [ons_decEdgeMicroDarts_sum_exponentX_external L u w hrev,
          ons_decWalkExternalDarts_cons_external huw p hrev]
        simp only [List.map_cons, List.sum_cons]
        have hexp : ons_dirExponentX w.2 =
            -ons_dirExponentX u.2 := by
          rw [hrev, ons_dirExponentX_dartRev]
        rw [ih', hexp]
        ring
      · have hint : ons_decInternalAdj u w := by
          change ons_decAdj L u w at huw
          exact huw.resolve_left hrev
        rw [ons_decEdgeMicroDarts_sum_exponentX_internal L u w hint]
        have hext :
            ons_decWalkExternalDarts (SimpleGraph.Walk.cons huw p) =
              ons_decWalkExternalDarts p := by
          simp [ons_decWalkExternalDarts, ons_decDartIsExternal, hrev]
        rw [hext, ih']
        ring

theorem ons_decExpandedDartList_sum_exponentY
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    ((ons_decExpandedDartList L p).map
      (fun a => ons_dirExponentY a.2)).sum =
        2 * (ons_dirExponentY v.2 - ons_dirExponentY u.2) +
          8 * ((ons_decWalkExternalDarts p).map
            (fun a => ons_dirExponentY a.2)).sum := by
  induction p with
  | nil => simp [ons_decExpandedDartList, ons_decWalkExternalDarts]
  | @cons u w v huw p ih =>
      simp only [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons, List.map_append, List.sum_append]
      have ih' :
          ((List.flatMap
            (fun a => ons_decEdgeMicroDarts L a.fst a.snd) p.darts).map
              (fun a => ons_dirExponentY a.2)).sum =
            2 * (ons_dirExponentY v.2 - ons_dirExponentY w.2) +
              8 * ((ons_decWalkExternalDarts p).map
                (fun a => ons_dirExponentY a.2)).sum := by
        simpa only [ons_decExpandedDartList] using ih
      by_cases hrev : w = ons_dartRev L u
      · rw [ons_decEdgeMicroDarts_sum_exponentY_external L u w hrev,
          ons_decWalkExternalDarts_cons_external huw p hrev]
        simp only [List.map_cons, List.sum_cons]
        have hexp : ons_dirExponentY w.2 =
            -ons_dirExponentY u.2 := by
          rw [hrev, ons_dirExponentY_dartRev]
        rw [ih', hexp]
        ring
      · have hint : ons_decInternalAdj u w := by
          change ons_decAdj L u w at huw
          exact huw.resolve_left hrev
        rw [ons_decEdgeMicroDarts_sum_exponentY_internal L u w hint]
        have hext :
            ons_decWalkExternalDarts (SimpleGraph.Walk.cons huw p) =
              ons_decWalkExternalDarts p := by
          simp [ons_decWalkExternalDarts, ons_decDartIsExternal, hrev]
        rw [hext, ih']
        ring

theorem ons_decWalkExternalDarts_sum_eq_cycleDartLoop
    {L : ℕ} [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle)
    (hsnd : q.snd = ons_dartRev L d) (f : ons_Dart L → ℤ) :
    ((ons_decWalkExternalDarts q).map f).sum =
      ∑ k, f (ons_decCycleDartLoop q k) := by
  let ext := ons_decWalkExternalDarts q
  have hhead : ext.head? = some d :=
    ons_decWalkExternalDarts_head q hq hsnd
  have hext : ext = d :: ext.tail := by
    apply List.eq_cons_of_mem_head?
    simpa [hhead]
  calc
    ((ons_decWalkExternalDarts q).map f).sum =
        f d + (ext.tail.map f).sum := by rw [show ons_decWalkExternalDarts q = ext from rfl, hext]; simp
    _ = f d + (ext.tail.reverse.map f).sum := by
      rw [List.map_reverse, List.sum_reverse]
    _ = ((ons_decCycleDartList q).map f).sum := by
      rw [ons_decCycleDartList_eq]
      rfl
    _ = ((List.ofFn (ons_decCycleDartLoop q)).map f).sum :=
      congrArg (fun l => (l.map f).sum)
        (ons_decCycleDartList_ofFn q).symm
    _ = ∑ k, f (ons_decCycleDartLoop q k) := by
      rw [List.map_ofFn, List.sum_ofFn]
      rfl

@[simp] theorem ons_decExpandedDartList_length
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decExpandedDartList L p).length = 4 * p.length := by
  induction p with
  | nil => simp [ons_decExpandedDartList]
  | @cons u w v huw p ih =>
      simp only [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons, List.length_append,
        ons_decEdgeMicroDarts_length, SimpleGraph.Walk.length_cons]
      have ih' :
          (List.flatMap (fun a => ons_decEdgeMicroDarts L a.fst a.snd)
            p.darts).length = 4 * p.length := by
        simpa only [ons_decExpandedDartList] using ih
      rw [ih']
      ring

theorem ons_decExpandedDartList_sites
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decExpandedDartList L p).map (fun a => a.1) =
      (ons_decEmbedWalk L p).support.dropLast := by
  rw [← (ons_decEmbedWalk L p).map_fst_darts]
  induction p with
  | nil => simp [ons_decExpandedDartList, ons_decEmbedWalk]
  | @cons u w v huw p ih =>
      rw [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons, List.map_append,
        ons_decEdgeMicroDarts_sites L u w huw, ons_decEmbedWalk,
        SimpleGraph.Walk.darts_append, List.map_append,
        ← (ons_decEdgeRoute L u w huw).map_fst_darts]
      apply congrArg (fun t =>
        (ons_decEdgeRoute L u w huw).darts.map (fun a => a.fst) ++ t)
      simpa only [ons_decExpandedDartList] using ih

theorem ons_decExpandedDartList_edges
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decExpandedDartList L p).map (ons_portEdge (8 * L)) =
      (ons_decEmbedWalk L p).edges := by
  induction p with
  | nil => simp [ons_decExpandedDartList, ons_decEmbedWalk]
  | @cons u w v huw p ih =>
      rw [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons, List.map_append,
        ons_decEdgeMicroDarts_edges L u w huw, ons_decEmbedWalk,
        SimpleGraph.Walk.edges_append]
      simpa only [ons_decExpandedDartList] using congrArg
        (fun t => (ons_decEdgeRoute L u w huw).edges ++ t) ih

theorem ons_decEdgeMicroDarts_isChain
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    List.IsChain
      (fun a b : ons_Dart (8 * L) =>
        ons_dirStep (8 * L) a.2 a.1 = b.1)
      (ons_decEdgeMicroDarts L d e) := by
  simp [ons_decEdgeMicroDarts]

theorem ons_decEdgeMicroDarts_last_step
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e)
    {a : ons_Dart (8 * L)}
    (ha : a ∈ (ons_decEdgeMicroDarts L d e).getLast?) :
    ons_dirStep (8 * L) a.2 a.1 = ons_decEmbedVertex L e := by
  have haeq :
      (ons_dirStep (8 * L) (ons_decEdgeRouteDirs L d e 2)
        (ons_dirStep (8 * L) (ons_decEdgeRouteDirs L d e 1)
          (ons_dirStep (8 * L) (ons_decEdgeRouteDirs L d e 0)
            (ons_decEmbedVertex L d))),
        ons_decEdgeRouteDirs L d e 3) = a := by
    simpa [ons_decEdgeMicroDarts] using ha
  subst a
  exact ons_decEdgeRoute_endpoint L d e hde

theorem ons_decExpandedDartList_head_site
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) {a : ons_Dart (8 * L)}
    (ha : a ∈ (ons_decExpandedDartList L p).head?) :
    a.1 = ons_decEmbedVertex L u := by
  cases p with
  | nil => simp [ons_decExpandedDartList] at ha
  | @cons u w v huw p =>
      have haeq : (ons_decEmbedVertex L u,
          ons_decEdgeRouteDirs L u w 0) = a := by
        simpa [ons_decExpandedDartList,
          ons_decEdgeMicroDarts] using ha
      exact (congrArg (fun z : ons_Dart (8 * L) => z.1) haeq).symm

theorem ons_decExpandedDartList_isChain
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    List.IsChain
      (fun a b : ons_Dart (8 * L) =>
        ons_dirStep (8 * L) a.2 a.1 = b.1)
      (ons_decExpandedDartList L p) := by
  induction p with
  | nil => exact .nil
  | @cons u w v huw p ih =>
      rw [ons_decExpandedDartList, SimpleGraph.Walk.darts_cons,
        List.flatMap_cons]
      apply (ons_decEdgeMicroDarts_isChain L u w huw).append ih
      intro a ha b hb
      calc
        ons_dirStep (8 * L) a.2 a.1 = ons_decEmbedVertex L w :=
          ons_decEdgeMicroDarts_last_step L u w huw ha
        _ = b.1 := (ons_decExpandedDartList_head_site L p hb).symm

theorem ons_decExpandedDartList_last_step
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) {a : ons_Dart (8 * L)}
    (ha : a ∈ (ons_decExpandedDartList L p).getLast?) :
    ons_dirStep (8 * L) a.2 a.1 = ons_decEmbedVertex L v := by
  induction p with
  | nil => simp [ons_decExpandedDartList] at ha
  | @cons u w v huw p ih =>
      cases p with
      | nil =>
          apply ons_decEdgeMicroDarts_last_step L u w huw
          simpa [ons_decExpandedDartList] using ha
      | @cons w z v hwz p =>
          apply ih
          simpa [ons_decExpandedDartList,
            ons_decEdgeMicroDarts] using ha

end StatMech.Onsager
