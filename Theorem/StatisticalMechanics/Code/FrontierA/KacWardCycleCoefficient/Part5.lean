/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleCoefficient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardUnitCycleReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardCycleCoefficient.Part5
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager

universe u


@[simp] theorem kwGraphCycleDartLoop_ofFn
    {V : Type u} {G : SimpleGraph V} {root : V}
    (p : G.Walk root root) :
    List.ofFn (kwGraphCycleDartLoop p) = p.darts := by
  exact List.ofFn_get p.darts

theorem kwGraphCycleDartLoop_valid
    {V : Type u} {G : SimpleGraph V} {root : V}
    (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    ∀ k, G.DartAdj (kwGraphCycleDartLoop p k)
      (kwGraphCycleDartLoop p (k + 1)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k
  unfold kwGraphCycleDartLoop SimpleGraph.DartAdj
  change (p.darts[k.1]'k.2).snd =
    (p.darts[(k + 1).1]'(k + 1).2).fst
  rw [SimpleGraph.Walk.darts_getElem_eq_getVert,
    SimpleGraph.Walk.darts_getElem_eq_getVert]
  change p.getVert (k.1 + 1) = p.getVert (k + 1).1
  by_cases hwrap : k.1 + 1 = p.darts.length
  · have hval : (k + 1).1 = 0 := by
      rw [Fin.val_add]
      have hlen : 3 ≤ p.darts.length := by
        simpa [SimpleGraph.Walk.length_darts] using hp.three_le_length
      simp [hwrap]
    rw [hval, hwrap, SimpleGraph.Walk.length_darts]
    simp
  · have hlt : k.1 + 1 < p.darts.length := by omega
    rw [Fin.val_add_one_of_lt' hlt]

theorem kwGraphCycleDartLoop_exponent
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwGraphLoopExponent G (kwGraphCycleDartLoop p) =
      ons_finsetExponent p.edges.toFinset := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let hvalid := kwGraphCycleDartLoop_valid p hp
  calc
    kwGraphLoopExponent G (kwGraphCycleDartLoop p) =
        Multiset.toFinsupp
          ((kwGraphLoopWalk G (kwGraphCycleDartLoop p) hvalid).edges :
            Multiset (Sym2 V)) :=
      (kwGraphLoopWalk_edgeCount G (kwGraphCycleDartLoop p) hvalid).symm
    _ = Multiset.toFinsupp (p.edges : Multiset (Sym2 V)) := by
      congr 2
      rw [kwGraphLoopWalk_edges, kwGraphCycleDartLoop_ofFn,
        ← SimpleGraph.Walk.edges]
    _ = ons_finsetExponent p.edges.toFinset :=
      (ons_finsetExponent_toFinset_eq_edgeCount
        p.edges hp.edges_nodup).symm

theorem kwGraphCycleDartLoop_nonbacktracking
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwGraphLoopNonbacktracking G (kwGraphCycleDartLoop p) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k
  refine ⟨kwGraphCycleDartLoop_valid p hp k, ?_⟩
  have hedgeNodup :
      (List.ofFn (fun i : Fin p.darts.length ↦
        (kwGraphCycleDartLoop p i).edge)).Nodup := by
    rw [List.ofFn_comp', kwGraphCycleDartLoop_ofFn]
    simpa [SimpleGraph.Walk.edges] using hp.edges_nodup
  have hedgeInj : Function.Injective
      (fun i : Fin p.darts.length ↦
        (kwGraphCycleDartLoop p i).edge) :=
    List.nodup_ofFn.mp hedgeNodup
  intro hedge
  have hindex : k = k + 1 := hedgeInj hedge
  have hzeroOne : (0 : Fin p.darts.length) = 1 := by
    apply add_left_cancel (a := k)
    simpa using hindex
  have hval := congrArg Fin.val hzeroOne
  have hlen : 3 ≤ p.length := hp.three_le_length
  have hdartsLen : p.darts.length = p.length := p.length_darts
  simp at hval
  omega

theorem kwGraphCycleDartLoop_scalar_eq_phaseProduct
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart → G.Dart → ℂ)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwGraphLoopScalar G phase (kwGraphCycleDartLoop p) =
      kwLoopPhaseProduct phase (kwGraphCycleDartLoop p) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  rw [kwGraphLoopScalar_eq_adjacency_mul_phaseProduct]
  have hadj : kwGraphLoopAdjacency G (kwGraphCycleDartLoop p) = 1 := by
    unfold kwGraphLoopAdjacency
    apply Finset.prod_eq_one
    intro k hk
    rw [if_pos (kwGraphCycleDartLoop_nonbacktracking G p hp k)]
  rw [hadj, one_mul]


theorem kwGraphFormalLogCoeff_cycle_of_phaseProduct_neg_one
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (hdeg : ∀ vertex, G.degree vertex ≤ 3)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle)
    (hphase :
      letI : NeZero p.darts.length :=
        ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
          (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
      kwLoopPhaseProduct embedding.turnPhase
        (kwGraphCycleDartLoop p) = -1) :
    kwGraphFormalLogCoeff G embedding.turnPhase
      (ons_finsetExponent p.edges.toFinset) = 1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  have hscalar : kwGraphLoopScalar G embedding.turnPhase
      (kwGraphCycleDartLoop p) = -1 := by
    rw [kwGraphCycleDartLoop_scalar_eq_phaseProduct G
      embedding.turnPhase p hp]
    exact hphase
  have hd : kwGraphCycleDartLoop p ∈
      kwGraphSquarefreeLoopFinset G embedding.turnPhase
        p.edges.toFinset := by
    rw [kwGraph_mem_squarefreeLoopFinset]
    exact ⟨kwGraphCycleDartLoop_exponent G p hp, by
      rw [hscalar]
      norm_num⟩
  exact kwGraphFormalLogCoeff_squarefree_eq_one_of_scalar_neg_one'
    G embedding hdeg p.edges.toFinset (kwGraphCycleDartLoop p) hd hscalar

end StatMech.FrontierA
