/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part7
import Def.StatisticalMechanics.Code.Onsager.DecorationLoopClassification.Part3


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_decLoopRootFinset_card_of_squarefree
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S) :
    (ons_decLoopRootFinset L d).card = 2 * n := by
  let f := fun k : Fin n ↦ ons_portEdge L (d k)
  have hfinj : Function.Injective f :=
    ons_decLoop_portEdge_injective_of_squarefree
      L d hvalid S hexponent
  have hdinj : Function.Injective d := by
    intro i j hij
    apply hfinj
    exact congrArg (ons_portEdge L) hij
  have hrevinj : Function.Injective
      (fun k : Fin n ↦ ons_dartRev L (d k)) := by
    intro i j hij
    apply hdinj
    have h := congrArg (ons_dartRev L) hij
    rw [ons_dartRev_involutive, ons_dartRev_involutive] at h
    exact h
  have hdisj : Disjoint (Finset.univ.image d)
      (Finset.univ.image (fun k ↦ ons_dartRev L (d k))) := by
    rw [Finset.disjoint_left]
    intro dart hdart hdartRev
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hdart
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hdartRev
    exact ons_decLoop_dart_ne_rev_of_squarefree
      L d hvalid S hexponent i j hj.symm
  unfold ons_decLoopRootFinset
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hdinj,
    Finset.card_image_of_injective _ hrevinj]
  simp
  omega

theorem ons_decSquarefreeLoop_root_edge_mem
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (S : Finset (ons_DecEdge L))
    {d : Fin n → ons_Dart L}
    (hd : d ∈ ons_decSquarefreeLoopFinset L a b S) :
    s(d 0, ons_dartRev L (d 0)) ∈ S := by
  rw [ons_mem_decSquarefreeLoopFinset] at hd
  let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) d hd.2
  let q := ons_decLoopWalk L d hvalid
  have hq : q.IsCycle :=
    ons_decLoopWalk_isCycle_of_squarefree L d hvalid S hd.1
  have hedge : s(d 0, ons_dartRev L (d 0)) ∈ q.edges := by
    have hfirst := q.mk_start_snd_mem_edges hq.not_nil
    rw [ons_decLoopWalk_snd L d hvalid] at hfirst
    exact hfirst
  rw [← ons_decLoopWalk_edges_toFinset_of_squarefree
    L d hvalid S hd.1]
  exact List.mem_toFinset.mpr hedge

theorem ons_external_root_mem_decLoopRootFinset
    (L : ℕ) [Fact (2 < L)] {n : ℕ} [NeZero n]
    (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
    (S : Finset (ons_DecEdge L))
    (hexponent : ons_decLoopExponent L d = ons_finsetExponent S)
    (root : ons_Dart L)
    (hroot : s(root, ons_dartRev L root) ∈ S) :
    root ∈ ons_decLoopRootFinset L d := by
  classical
  let q := ons_decLoopWalk L d hvalid
  have hqedge : s(root, ons_dartRev L root) ∈ q.edges.toFinset := by
    rw [ons_decLoopWalk_edges_toFinset_of_squarefree
      L d hvalid S hexponent]
    exact hroot
  have hport : ons_portEdge L root ∈ ons_walkOriginalEdges q := by
    unfold ons_walkOriginalEdges ons_walkExternalEdges
      ons_decoratedExternalEdges
    rw [Finset.mem_image]
    refine ⟨s(root, ons_dartRev L root), ?_,
      ons_decEdgeProjection_external L root⟩
    exact Finset.mem_filter.mpr ⟨hqedge, ⟨root, rfl⟩⟩
  rw [← ons_decWalkExternalDarts_image_portEdge q,
    Finset.mem_image] at hport
  obtain ⟨dart, hdart, hprojection⟩ := hport
  rw [ons_decLoopWalk_externalDarts L d hvalid,
    List.mem_toFinset, List.mem_ofFn] at hdart
  obtain ⟨k, hk⟩ := hdart
  rcases (ons_portEdge_eq_iff L root dart).mp hprojection with heq | heq
  ·
    unfold ons_decLoopRootFinset
    apply Finset.mem_union.mpr
    left
    apply Finset.mem_image.mpr
    refine ⟨-k, Finset.mem_univ _, ?_⟩
    calc
      d (-k) = dart := by
        simpa [ons_decGeometricLoopStates] using hk
      _ = root := heq
  ·
    unfold ons_decLoopRootFinset
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨-k, Finset.mem_univ _, ?_⟩
    calc
      ons_dartRev L (d (-k)) = ons_dartRev L dart := by
        exact congrArg (ons_dartRev L)
          (by simpa [ons_decGeometricLoopStates] using hk)
      _ = root := by
        rw [heq, ons_dartRev_involutive]

end StatMech.Onsager
