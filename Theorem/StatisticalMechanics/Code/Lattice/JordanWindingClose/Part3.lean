/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanCrossingCount.Part7
import Def.StatisticalMechanics.Code.Lattice.JordanWindingClose.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jwc_cyclePath_le {V : Type*} [DecidableEq V] {K : SimpleGraph V} {x y : V}
    (hreach : K.Reachable x y) : jwc_cyclePath hreach ≤ K := by
  intro a b hab
  rw [jwc_cyclePath, Subgraph.spanningCoe_adj] at hab
  exact (hreach.symm).some.toPath.val.toSubgraph.adj_sub hab


theorem jwc_cyclePath_sup_edge_isEven {V : Type*} [Finite V] [DecidableEq V] {K : SimpleGraph V}
    {x y : V} (hreach : K.Reachable x y) (hne : x ≠ y) (hnadj : ¬ K.Adj x y) :
    jcx_IsEven (jwc_cyclePath hreach ⊔ edge x y) := by
  classical
  set q : K.Walk y x := (hreach.symm).some.toPath.val with hq
  have hqpath : q.IsPath := (hreach.symm).some.toPath.prop
  set G := K ⊔ edge x y with hG
  have hxy_adj : G.Adj x y := by
    rw [hG, sup_adj]; right; rw [edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
  set qG : G.Walk y x := q.mapLe le_sup_left with hqG
  have hqGpath : qG.IsPath := (SimpleGraph.Walk.mapLe_isPath le_sup_left).mpr hqpath
  set cyc : G.Walk x x := Walk.cons hxy_adj qG with hcyc
  have hcycIsCycle : cyc.IsCycle := by
    rw [hcyc, Walk.cons_isCycle_iff]
    refine ⟨hqGpath, ?_⟩
    intro hmem
    rw [hqG, SimpleGraph.Walk.edges_mapLe_eq_edges] at hmem
    exact hnadj (q.adj_of_mem_edges hmem)
  have hcyclesCyc : cyc.toSubgraph.spanningCoe.IsCycles :=
    hcycIsCycle.isCycles_spanningCoe_toSubgraph
  have hspanEq : qG.toSubgraph.spanningCoe = jwc_cyclePath hreach := by
    rw [jwc_cyclePath, ← hq]
    ext a b
    rw [Subgraph.spanningCoe_adj, hqG, Subgraph.spanningCoe_adj,
      SimpleGraph.Walk.adj_toSubgraph_mapLe]
  have heq : cyc.toSubgraph.spanningCoe = jwc_cyclePath hreach ⊔ edge x y := by
    rw [hcyc, jvp_consSpanningCoe hxy_adj qG, hspanEq, sup_comm]
  rw [← heq]
  exact jcx_isEven_of_isCycles hcyclesCyc


theorem jwc_syncMerge (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (hKle : K ≤ P.G)
    {x y : P.V} (hadjG : P.G.Adj x y) (hnotK : ¬ K.Adj x y) {f0 g0 : Site 2}
    (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(P.emb x, P.emb y)) (hreach : K.Reachable x y) :
    ¬ ((whb_faceRegion (jei_pushGraph P K)).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  classical
  haveI : Finite P.V := P.finV
  haveI : DecidableEq P.V := P.decV
  have hne : x ≠ y := hadjG.ne
  set Cw := jwc_cyclePath hreach with hCw
  have hCwle : Cw ≤ K := jwc_cyclePath_le hreach
  have hCwG : Cw ≤ P.G := hCwle.trans hKle
  haveI : DecidableRel (Cw ⊔ edge x y).Adj := Classical.decRel _
  have hev : jcx_IsEven (Cw ⊔ edge x y) := jwc_cyclePath_sup_edge_isEven hreach hne hnotK
  have hCwEdge_le : Cw ⊔ edge x y ≤ P.G := by
    refine sup_le hCwG ?_
    intro a b hab; rw [edge_adj] at hab
    rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadjG
    · exact hadjG.symm
  
  have hccPush : jce_ClosedContour (jei_pushGraph P (Cw ⊔ edge x y)).edgeSet :=
    jcx_pushGraph_closedContour P (Cw ⊔ edge x y) hCwEdge_le hev
  
  have hcontourEq : ((insert (sharedPrimalEdge f0 g0)
        (jei_pushGraph_edgeSet_finite P Cw).toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))
      = (jei_pushGraph P (Cw ⊔ edge x y)).edgeSet := by
    rw [Finset.coe_insert, Set.Finite.coe_toFinset, hshared,
      jei_pushGraph_sup_edge P Cw x y hne, SimpleGraph.edgeSet_sup]
    ext e
    refine e.ind (fun a c => ?_)
    have hpq : P.emb x ≠ P.emb y := fun h => hne (P.emb.injective h)
    simp only [Set.mem_insert_iff, Set.mem_union, SimpleGraph.mem_edgeSet, SimpleGraph.edge_adj]
    constructor
    · rintro (h | h)
      · right; rw [Sym2.eq_iff] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨Or.inl ⟨rfl, rfl⟩, hpq⟩
        · exact ⟨Or.inr ⟨rfl, rfl⟩, Ne.symm hpq⟩
      · exact Or.inl h
    · rintro (h | ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩)
      · exact Or.inr h
      · left; rfl
      · left; rw [Sym2.eq_swap]
  have hccFinset : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) (jei_pushGraph_edgeSet_finite P Cw).toFinset
        : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) := by
    rw [hcontourEq]; exact hccPush
  
  have hsepCw := jwc_syncMerge_of_closedContour P Cw hCwG hfg hccFinset
  
  exact jwc_separated_mono (jwc_pushGraph_mono P hCwle) hsepCw


end Lattice
end StatMech
