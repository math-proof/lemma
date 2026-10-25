/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardCycleCoefficient.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager

universe u


theorem kwGraphLoopRootFinset_card_of_squarefree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
    (kwGraphLoopRootFinset loop).card = 2 * n := by
  rw [kwGraph_mem_squarefreeLoopFinset] at hloop
  let hvalid := kwGraphLoop_valid_of_scalar_ne_zero G phase loop hloop.2
  have htrail := kwGraphLoopWalk_isTrail_and_edges
    G loop hvalid S hloop.1
  have hedgeNodup :
      ((List.ofFn loop).map SimpleGraph.Dart.edge).Nodup := by
    rw [← kwGraphLoopWalk_edges G loop hvalid]
    exact htrail.1.edges_nodup
  rw [← List.ofFn_comp'] at hedgeNodup
  have hedgeInj : Function.Injective
      (fun k : Fin n ↦ (loop k).edge) :=
    List.nodup_ofFn.mp hedgeNodup
  have hloopInj : Function.Injective loop := by
    intro i j hij
    exact hedgeInj (congrArg (fun dart : G.Dart ↦ dart.edge) hij)
  have hrevInj : Function.Injective (fun k ↦ (loop k).symm) := by
    intro i j hij
    apply hloopInj
    simpa using congrArg SimpleGraph.Dart.symm hij
  have hdisj : Disjoint (Finset.univ.image loop)
      (Finset.univ.image (fun k ↦ (loop k).symm)) := by
    rw [Finset.disjoint_left]
    intro dart hdart hdartRev
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hdart
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hdartRev
    have hij : i = j := by
      apply hedgeInj
      calc
        (loop i).edge = ((loop j).symm).edge :=
          congrArg (fun dart : G.Dart ↦ dart.edge) hj.symm
        _ = (loop j).edge := SimpleGraph.Dart.edge_symm _
    subst j
    exact (loop i).symm_ne hj
  unfold kwGraphLoopRootFinset
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hloopInj,
    Finset.card_image_of_injective _ hrevInj]
  simp
  omega

theorem kwGraph_squarefreeLoop_root_edge_mem
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S) :
    (loop 0).edge ∈ S := by
  rw [kwGraph_mem_squarefreeLoopFinset] at hloop
  let hvalid := kwGraphLoop_valid_of_scalar_ne_zero G phase loop hloop.2
  have hedges := (kwGraphLoopWalk_isTrail_and_edges
    G loop hvalid S hloop.1).2
  rw [← hedges, kwGraphLoopWalk_edges]
  simp

theorem kwGraph_root_mem_loopRootFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {n : ℕ} [NeZero n] (S : Finset (Sym2 V))
    {loop : Fin n → G.Dart}
    (hloop : loop ∈ kwGraphSquarefreeLoopFinset G phase S)
    (root : G.Dart) (hroot : root.edge ∈ S) :
    root ∈ kwGraphLoopRootFinset loop := by
  rw [kwGraph_mem_squarefreeLoopFinset] at hloop
  let hvalid := kwGraphLoop_valid_of_scalar_ne_zero G phase loop hloop.2
  have hedges := (kwGraphLoopWalk_isTrail_and_edges
    G loop hvalid S hloop.1).2
  rw [← hedges, kwGraphLoopWalk_edges, List.mem_toFinset,
    List.mem_map] at hroot
  obtain ⟨dart, hdart, hedge⟩ := hroot
  rw [List.mem_ofFn] at hdart
  obtain ⟨k, rfl⟩ := hdart
  rcases (SimpleGraph.dart_edge_eq_iff root (loop k)).mp hedge.symm with heq | heq
  · subst root
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨k, Finset.mem_univ _, rfl⟩)
  · subst root
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨k, Finset.mem_univ _, rfl⟩)


end StatMech.FrontierA
