/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part12


namespace StatMech.Onsager

theorem ons_decEmbedWalk_tail_support
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decEmbedWalk L p).support.tail =
      p.darts.flatMap (ons_decDartSegment L) := by
  induction p with
  | nil => simp [ons_decEmbedWalk]
  | @cons u w v huw p ih =>
      simp only [ons_decEmbedWalk, SimpleGraph.Walk.tail_support_append,
        SimpleGraph.Walk.darts_cons, List.flatMap_cons, ih]
      rfl

theorem ons_decEmbedWalk_length_aux
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decEmbedWalk L p).length = 4 * p.length := by
  induction p with
  | nil => simp [ons_decEmbedWalk]
  | @cons u w v huw p ih =>
      simp only [ons_decEmbedWalk, SimpleGraph.Walk.length_append,
        ons_decEdgeRoute_length, ih, SimpleGraph.Walk.length_cons]
      ring

theorem ons_decEmbedWalk_tail_nodup_of_isCycle
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (p : (ons_decGraph L).Walk d d) (hp : p.IsCycle) :
    (ons_decEmbedWalk L p).support.tail.Nodup := by
  rw [ons_decEmbedWalk_tail_support]
  apply List.nodup_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro a ha
    exact ons_decDartSegment_nodup L a
  · have hedge : p.darts.Pairwise (fun a b => a.edge ≠ b.edge) := by
      have h := hp.edges_nodup
      change (p.darts.map (fun a => a.edge)).Nodup at h
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at h
      exact h
    have hsndMap : (p.darts.map (fun a => a.snd)).Nodup := by
      rw [SimpleGraph.Walk.map_snd_darts]
      exact hp.support_nodup
    have hsnd : p.darts.Pairwise (fun a b => a.snd ≠ b.snd) := by
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hsndMap
      exact hsndMap
    have hboth : p.darts.Pairwise
        (fun a b => a.edge ≠ b.edge ∧ a.snd ≠ b.snd) :=
      List.pairwise_and_iff.mpr ⟨hedge, hsnd⟩
    exact hboth.imp (fun hab =>
      ons_decDartSegment_disjoint L _ _ hab.1 hab.2)


theorem ons_decEmbedWalk_isCycle
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (p : (ons_decGraph L).Walk d d) (hp : p.IsCycle) :
    (ons_decEmbedWalk L p).IsCycle := by
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  have hlen : 3 ≤ (ons_decEmbedWalk L p).length := by
    rw [ons_decEmbedWalk_length_aux]
    have := hp.three_le_length
    omega
  refine ⟨?_, hlen⟩
  apply SimpleGraph.Walk.IsPath.mk'
  have hnotnil : ¬(ons_decEmbedWalk L p).Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  rw [(ons_decEmbedWalk L p).support_tail_of_not_nil hnotnil]
  exact ons_decEmbedWalk_tail_nodup_of_isCycle L p hp

@[simp] theorem ons_decEmbedWalk_length
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decEmbedWalk L p).length = 4 * p.length := by
  exact ons_decEmbedWalk_length_aux L p

end StatMech.Onsager
