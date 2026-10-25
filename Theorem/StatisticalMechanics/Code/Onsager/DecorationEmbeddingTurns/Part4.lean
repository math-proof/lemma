/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbeddingDisjoint
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbeddingTurns.Part4


namespace StatMech.Onsager

theorem ons_decExpandedGeometricLoop_sum_exponentX
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    ∑ k, ons_dirExponentX (ons_decExpandedGeometricLoop L q k).2 =
      8 * ((ons_decWalkExternalDarts q).map
        (fun a => ons_dirExponentX a.2)).sum := by
  let f : ons_Dart (8 * L) → ℤ := fun a => ons_dirExponentX a.2
  calc
    ∑ k, f (ons_decExpandedGeometricLoop L q k) =
        (List.ofFn (fun k => f (ons_decExpandedGeometricLoop L q k))).sum :=
      List.sum_ofFn.symm
    _ = ((List.ofFn (ons_decExpandedGeometricLoop L q)).map f).sum := by
      simp [List.map_ofFn, Function.comp_def]
    _ = ((ons_decExpandedDartList L q).map f).sum := by
      change ((List.ofFn (ons_decExpandedDartList L q).get).map f).sum = _
      rw [List.ofFn_get]
    _ = _ := by
      simpa [f] using ons_decExpandedDartList_sum_exponentX L q

theorem ons_decExpandedGeometricLoop_sum_exponentY
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    ∑ k, ons_dirExponentY (ons_decExpandedGeometricLoop L q k).2 =
      8 * ((ons_decWalkExternalDarts q).map
        (fun a => ons_dirExponentY a.2)).sum := by
  let f : ons_Dart (8 * L) → ℤ := fun a => ons_dirExponentY a.2
  calc
    ∑ k, f (ons_decExpandedGeometricLoop L q k) =
        (List.ofFn (fun k => f (ons_decExpandedGeometricLoop L q k))).sum :=
      List.sum_ofFn.symm
    _ = ((List.ofFn (ons_decExpandedGeometricLoop L q)).map f).sum := by
      simp [List.map_ofFn, Function.comp_def]
    _ = ((ons_decExpandedDartList L q).map f).sum := by
      change ((List.ofFn (ons_decExpandedDartList L q).get).map f).sum = _
      rw [List.ofFn_get]
    _ = _ := by
      simpa [f] using ons_decExpandedDartList_sum_exponentY L q

theorem ons_decExpandedGeometricLoop_edgeSet
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    ons_dartEdgeSet (ons_decExpandedGeometricLoop L q) =
      (ons_decEmbedWalk L q).edges.toFinset := by
  classical
  rw [← ons_decExpandedDartList_edges]
  ext e
  simp [ons_dartEdgeSet, ons_decExpandedGeometricLoop]

theorem ons_decExpandedRoot_eq_zero
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    ons_decExpandedRoot L q = ons_decExpandedGeometricLoop L q 0 := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  have hne : ons_decExpandedDartList L q ≠ [] :=
    List.ne_nil_iff_length_pos.mpr
      (ons_decExpandedDartList_length_pos L q hq)
  obtain ⟨a, t, hat⟩ := List.exists_cons_of_ne_nil hne
  simp [ons_decExpandedRoot, ons_decExpandedGeometricLoop, hat]

theorem ons_decExpandedGeometricLoop_valid
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    letI : NeZero (ons_decExpandedDartList L q).length :=
      ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
    ∀ k : Fin (ons_decExpandedDartList L q).length,
      ons_dirStep (8 * L) (ons_decExpandedGeometricLoop L q k).2
          (ons_decExpandedGeometricLoop L q k).1 =
        (ons_decExpandedGeometricLoop L q (k + 1)).1 := by
  letI : NeZero (ons_decExpandedDartList L q).length :=
    ⟨Nat.ne_of_gt (ons_decExpandedDartList_length_pos L q hq)⟩
  apply ons_isChain_closed_ofFn
    (R := fun a b : ons_Dart (8 * L) =>
      ons_dirStep (8 * L) a.2 a.1 = b.1)
    (ons_decExpandedGeometricLoop L q)
  change List.IsChain _
    (List.ofFn (ons_decExpandedDartList L q).get ++
      [(ons_decExpandedDartList L q).get 0])
  rw [List.ofFn_get]
  have hroot : ons_decExpandedRoot L q =
      (ons_decExpandedDartList L q).get 0 := by
    simpa [ons_decExpandedGeometricLoop] using
      ons_decExpandedRoot_eq_zero L q hq
  rw [← hroot]
  exact ons_decExpandedDartList_isChain_closed L q hq

theorem ons_decExpandedGeometricLoop_site_injective
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) (hq : q.IsCycle) :
    Function.Injective
      (fun k : Fin (ons_decExpandedDartList L q).length =>
        (ons_decExpandedGeometricLoop L q k).1) := by
  have hemb := ons_decEmbedWalk_isCycle L q hq
  have hdrop : (ons_decEmbedWalk L q).support.dropLast.Nodup := by
    have hrev := ((SimpleGraph.Walk.isCycle_def
      (ons_decEmbedWalk L q).reverse).mp hemb.reverse).2.2
    simpa [SimpleGraph.Walk.support_reverse] using hrev
  have hsites : ((ons_decExpandedDartList L q).map (fun a => a.1)).Nodup := by
    rw [ons_decExpandedDartList_sites]
    exact hdrop
  intro i j hij
  have hinjOn := List.inj_on_of_nodup_map hsites
  have hget : (ons_decExpandedDartList L q).get i =
      (ons_decExpandedDartList L q).get j :=
    hinjOn (List.get_mem _ i) (List.get_mem _ j) (by
      simpa [ons_decExpandedGeometricLoop] using hij)
  exact List.nodup_iff_injective_get.mp
    (hsites.of_map (fun a => a.1)) hget

end StatMech.Onsager
