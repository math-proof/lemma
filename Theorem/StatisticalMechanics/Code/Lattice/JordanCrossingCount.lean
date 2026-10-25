/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCrossingCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenStep
import Theorem.StatisticalMechanics.Code.Lattice.JordanIsCyclesCount.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanGeneralCount.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanCrossingCount
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jcx_isEven_of_isCycles {V : Type*} [Finite V] {K : SimpleGraph V} (hcyc : K.IsCycles) :
    jcx_IsEven K :=
  fun v => jvp_isCycles_even hcyc v


theorem jcx_cycle_neighborCard {V : Type*} [Finite V] {K : SimpleGraph V}
    {v : V} (p : K.Walk v v) (hp : p.IsCycle) (u : V) :
    Nat.card (p.toSubgraph.spanningCoe.neighborSet u) = 0 ∨
      Nat.card (p.toSubgraph.spanningCoe.neighborSet u) = 2 := by
  have hcyc := hp.isCycles_spanningCoe_toSubgraph
  rw [Nat.card_coe_set_eq]
  by_cases hne : (p.toSubgraph.spanningCoe.neighborSet u).Nonempty
  · right; exact hcyc hne
  · left
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]; simp


theorem jcx_neighborSet_deleteCycle {V : Type*} [DecidableEq V] (K : SimpleGraph V)
    {v : V} (p : K.Walk v v) (u : V) :
    (K.deleteEdges p.toSubgraph.edgeSet).neighborSet u =
      K.neighborSet u \ p.toSubgraph.spanningCoe.neighborSet u := by
  ext w
  simp only [mem_neighborSet, deleteEdges_adj, Set.mem_diff, Subgraph.spanningCoe_adj]
  constructor
  · rintro ⟨hK, hnotin⟩
    exact ⟨hK, fun hadj => hnotin (by rw [Subgraph.mem_edgeSet]; exact hadj)⟩
  · rintro ⟨hK, hnotin⟩
    refine ⟨hK, fun hin => hnotin ?_⟩
    rwa [Subgraph.mem_edgeSet] at hin


theorem jcx_isEven_deleteCycle {V : Type*} [Finite V] [DecidableEq V] {K : SimpleGraph V}
    (hev : jcx_IsEven K) {v : V} (p : K.Walk v v) (hp : p.IsCycle) :
    jcx_IsEven (K.deleteEdges p.toSubgraph.edgeSet) := by
  classical
  intro u
  
  have hsub : p.toSubgraph.spanningCoe.neighborSet u ⊆ K.neighborSet u := by
    intro w hw
    rw [mem_neighborSet, Subgraph.spanningCoe_adj] at hw
    rw [mem_neighborSet]; exact p.toSubgraph.adj_sub hw
  have hset := jcx_neighborSet_deleteCycle K p u
  
  have hcardK := hev u
  have hcardCyc := jcx_cycle_neighborCard p hp u
  haveI : Finite (K.neighborSet u) := Set.finite_coe_iff.mpr (Set.toFinite _)
  have hdiff : Nat.card ((K.deleteEdges p.toSubgraph.edgeSet).neighborSet u)
      = Nat.card (K.neighborSet u) - Nat.card (p.toSubgraph.spanningCoe.neighborSet u) := by
    rw [hset, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
      Set.ncard_diff hsub (Set.toFinite _)]
  rw [hdiff]
  rcases hcardCyc with h0 | h2
  · rw [h0]; simpa using hcardK
  · rw [h2]
    rcases hcardK with ⟨k, hk⟩
    
    rw [hk]; exact ⟨k - 1, by omega⟩


theorem jcx_pushGraph_closedContour (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    [DecidableRel K.Adj] (hKle : K ≤ P.G) (hev : jcx_IsEven K) :
    jce_ClosedContour (jei_pushGraph P K).edgeSet := by
  classical
  haveI : Fintype P.V := Fintype.ofFinite _
  haveI hlf : SimpleGraph.LocallyFinite (jei_pushGraph P K) := jfc_pushGraph_locallyFinite P K hKle
  haveI hlfK : SimpleGraph.LocallyFinite K := fun v => Fintype.ofFinite _
  have hsub : jei_pushGraph P K ≤ hypercubicLattice 2 := jfc_pushGraph_le_lattice P K hKle
  intro s
  rw [jeb_jce_degree_eq_degree (jei_pushGraph P K) hsub s]
  by_cases hs : ∃ v : P.V, P.emb v = s
  · obtain ⟨v, rfl⟩ := hs
    have hdeg : (jei_pushGraph P K).degree (P.emb v) = K.degree v := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
      symm
      apply Finset.card_bij (fun w _ => P.emb w)
      · intro w hw
        rw [SimpleGraph.mem_neighborFinset] at hw
        rw [SimpleGraph.mem_neighborFinset, jei_pushGraph_adj]
        exact ⟨v, w, hw, rfl, rfl⟩
      · intro a _ b _ h; exact P.emb.injective h
      · intro w hw
        rw [SimpleGraph.mem_neighborFinset, jei_pushGraph_adj] at hw
        obtain ⟨x, y, hxy, hx, hy⟩ := hw
        have hxv : x = v := P.emb.injective hx
        subst hxv
        exact ⟨y, by rw [SimpleGraph.mem_neighborFinset]; exact hxy, hy⟩
    rw [hdeg]
    have h := hev v
    rwa [Nat.card_eq_fintype_card, SimpleGraph.card_neighborSet_eq_degree] at h
  · have hzero : (jei_pushGraph P K).degree s = 0 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero,
        Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [SimpleGraph.mem_neighborFinset, jei_pushGraph_adj] at hw
      obtain ⟨x, y, _, hx, _⟩ := hw
      exact hs ⟨x, hx⟩
    rw [hzero]; exact ⟨0, rfl⟩


theorem jcx_addWalk_tc (P : PlanarZ2Subgraph) :
    ∀ {x y : P.V} (q : P.G.Walk x y) (H : SimpleGraph P.V), q.IsPath →
      (∀ u ∈ q.support, u ≠ y → ∀ w, ¬ H.Adj u w) →
      jic_tc P (H ⊔ q.toSubgraph.spanningCoe) = jic_tc P H := by
  intro x y q
  induction q with
  | nil =>
    intro H _ _; congr 1; exact jvp_sup_nil_spanningCoe x H
  | @cons x z y hadj p ih =>
    intro H hpath hiso
    obtain ⟨hpp, hxns⟩ := (Walk.cons_isPath_iff hadj p).mp hpath
    have hiso_p : ∀ u ∈ p.support, u ≠ y → ∀ w, ¬ H.Adj u w := fun u hu hne w =>
      hiso u (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hu) hne w
    set Hp := H ⊔ p.toSubgraph.spanningCoe with hHp
    have ihHp : jic_tc P Hp = jic_tc P H := ih H hpp hiso_p
    have hxinsupp : x ∈ (Walk.cons hadj p).support := by
      rw [Walk.support_cons]; exact List.mem_cons_self
    have hxney : x ≠ y := by intro h; subst h; exact hxns (Walk.end_mem_support p)
    have hxiso : ∀ w, ¬ Hp.Adj x w := by
      intro w hadjw; rw [hHp, sup_adj] at hadjw
      rcases hadjw with h | h
      · exact hiso x hxinsupp hxney w h
      · rw [Subgraph.spanningCoe_adj] at h
        exact hxns (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert h))
    have hxz : x ≠ z := fun h => hxns (h ▸ Walk.start_mem_support p)
    have hunion : H ⊔ (Walk.cons hadj p).toSubgraph.spanningCoe = Hp ⊔ edge x z := by
      rw [jvp_consSpanningCoe hadj p, hHp]; ac_rfl
    have hlat : (hypercubicLattice 2).Adj (P.emb x) (P.emb z) := P.isSub hadj
    have hkeep := jic_tc_sup_edge_keep P Hp hxz hlat hxiso
    rw [hunion, hkeep, ihHp]


theorem jcx_walk_spanningCoe_reachable {V : Type*} {G : SimpleGraph V} {x y : V} (q : G.Walk x y) :
    q.toSubgraph.spanningCoe.Reachable x y := by
  induction q with
  | nil => exact Reachable.refl _
  | @cons a b c hadj p ih =>
    have hstep : (Walk.cons hadj p).toSubgraph.spanningCoe.Adj a b := by
      rw [Subgraph.spanningCoe_adj, Walk.toSubgraph]; left; rw [subgraphOfAdj_adj]
    have hmono : p.toSubgraph.spanningCoe ≤ (Walk.cons hadj p).toSubgraph.spanningCoe := by
      intro s t hst; rw [Subgraph.spanningCoe_adj] at hst ⊢
      rw [Walk.toSubgraph]; right; exact hst
    exact hstep.reachable.trans (ih.mono hmono)


theorem jcx_tc_deleteCycle (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) [DecidableRel K.Adj]
    (hKle : K ≤ P.G) (hev : jcx_IsEven K) {v : P.V} (p : K.Walk v v) (hp : p.IsCycle)
    (hiso : ∀ u ∈ p.support, u ≠ v →
      ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w) :
    jic_tc P K = jic_tc P (K.deleteEdges p.toSubgraph.edgeSet) + 1 := by
  classical
  haveI : Finite P.V := P.finV
  haveI hlfK : SimpleGraph.LocallyFinite K := fun w => Fintype.ofFinite _
  obtain ⟨z, hadj, q, hpeq, hqpath⟩ : ∃ (z : P.V) (hadj : K.Adj v z) (q : K.Walk z v),
      p = Walk.cons hadj q ∧ q.IsPath := by
    cases p with
    | nil => exact absurd Walk.nil_nil hp.not_nil
    | cons hadj q => rw [Walk.cons_isCycle_iff] at hp; exact ⟨_, hadj, q, rfl, hp.1⟩
  set K'' := K.deleteEdges p.toSubgraph.edgeSet with hK''
  have hqsub : ∀ u ∈ q.support, u ∈ p.support := by
    intro u hu; rw [hpeq, Walk.support_cons]; exact List.mem_cons_of_mem _ hu
  have hisoQ : ∀ u ∈ q.support, u ≠ v → ∀ w, ¬ K''.Adj u w :=
    fun u hu hne w => hiso u (hqsub u hu) hne w
  set qG : P.G.Walk z v := q.mapLe hKle with hqG
  have hqGpath : qG.IsPath := (SimpleGraph.Walk.mapLe_isPath hKle).mpr hqpath
  have hsupp : qG.support = q.support := by
    rw [hqG]; exact SimpleGraph.Walk.support_mapLe_eq_support hKle q
  have hspan : qG.toSubgraph.spanningCoe = q.toSubgraph.spanningCoe := by
    ext w x
    rw [hqG, Subgraph.spanningCoe_adj, Subgraph.spanningCoe_adj,
      SimpleGraph.Walk.adj_toSubgraph_mapLe]
  have hisoQG : ∀ u ∈ qG.support, u ≠ v → ∀ w, ¬ K''.Adj u w := by
    intro u hu hne w; rw [hsupp] at hu; exact hisoQ u hu hne w
  have haddK'' : K'' ≤ P.G := (deleteEdges_le _).trans hKle
  have haddwalk := jcx_addWalk_tc P qG K'' hqGpath hisoQG
  set Kq := K'' ⊔ qG.toSubgraph.spanningCoe with hKqdef
  have hpspan : p.toSubgraph.spanningCoe = q.toSubgraph.spanningCoe ⊔ edge v z := by
    rw [hpeq]; exact jvp_consSpanningCoe hadj q
  have hKeq : K = K'' ⊔ p.toSubgraph.spanningCoe := by
    ext a c
    simp only [hK'', sup_adj, deleteEdges_adj, Subgraph.spanningCoe_adj]
    constructor
    · intro hKac
      by_cases hin : s(a, c) ∈ p.toSubgraph.edgeSet
      · right; rw [Subgraph.mem_edgeSet] at hin; exact hin
      · left; exact ⟨hKac, hin⟩
    · rintro (⟨hh, _⟩ | hh)
      · exact hh
      · exact p.toSubgraph.adj_sub hh
  have hKeq2 : K = Kq ⊔ edge v z := by rw [hKeq, hpspan, hKqdef, hspan]; ac_rfl
  
  have hqreach : Kq.Reachable z v := by
    have hle : qG.toSubgraph.spanningCoe ≤ Kq := le_sup_right
    exact (jcx_walk_spanningCoe_reachable qG).mono hle
  have hqspanle : q.toSubgraph.spanningCoe ≤ K := by
    intro a c h; exact q.toSubgraph.adj_sub (by rwa [Subgraph.spanningCoe_adj] at h)
  have hKqle : Kq ≤ P.G := by
    rw [hKqdef]
    exact sup_le haddK'' (by rw [hspan]; exact hqspanle.trans hKle)
  
  have hvz_in_p : s(v, z) ∈ p.toSubgraph.edgeSet := by
    rw [hpeq]
    have : s(v, z) ∈ (Walk.cons hadj q).edges := by
      rw [Walk.edges_cons]; exact List.mem_cons_self
    rw [(Walk.cons hadj q).mem_edges_toSubgraph]; exact this
  have hnotKq : ¬ Kq.Adj v z := by
    rw [hKqdef, sup_adj]
    rintro (h | h)
    · rw [hK'', deleteEdges_adj] at h
      exact h.2 hvz_in_p
    · rw [hspan, Subgraph.spanningCoe_adj, q.adj_toSubgraph_iff_mem_edges] at h
      have hpc : p.IsCycle := hp
      rw [hpeq, Walk.cons_isCycle_iff] at hpc
      exact hpc.2 (by rw [Sym2.eq_swap] at h ⊢; exact h)
  have hadjG : P.G.Adj v z := hKle hadj
  have hccK : jce_ClosedContour (jei_pushGraph P (Kq ⊔ edge v z)).edgeSet := by
    rw [← hKeq2]; exact jcx_pushGraph_closedContour P K hKle hev
  haveI : DecidableRel Kq.Adj := Classical.decRel _
  have hclose := jic_tc_close_edge P Kq hKqle hadjG hnotKq hqreach.symm hccK
  rw [hKeq2, hclose, hKqdef, haddwalk]


theorem jcx_addWalk_faceCount {V : Type*} [Finite V] [DecidableEq V] {G : SimpleGraph V} :
    ∀ {x y : V} (q : G.Walk x y) (H : SimpleGraph V), q.IsPath →
      (∀ u ∈ q.support, u ≠ y → ∀ w, ¬ H.Adj u w) →
      faceCount (H ⊔ q.toSubgraph.spanningCoe) = faceCount H ∧
        (∀ u ∈ q.support, (H ⊔ q.toSubgraph.spanningCoe).Reachable x u) := by
  intro x y q
  induction q with
  | nil =>
    intro H _ _
    refine ⟨by rw [jvp_sup_nil_spanningCoe], ?_⟩
    intro u hu
    rw [Walk.support_nil, List.mem_singleton] at hu; subst hu
    exact (jvp_sup_nil_spanningCoe _ H).symm ▸ Reachable.refl u
  | @cons x z y hadj p ih =>
    intro H hpath hiso
    obtain ⟨hpp, hxns⟩ := (Walk.cons_isPath_iff hadj p).mp hpath
    have hiso_p : ∀ u ∈ p.support, u ≠ y → ∀ w, ¬ H.Adj u w := fun u hu hne w =>
      hiso u (by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hu) hne w
    obtain ⟨ihface, ihreach⟩ := ih H hpp hiso_p
    set Hp := H ⊔ p.toSubgraph.spanningCoe with hHp
    have hunion : H ⊔ (Walk.cons hadj p).toSubgraph.spanningCoe = Hp ⊔ edge x z := by
      rw [jvp_consSpanningCoe hadj p, hHp]; ac_rfl
    have hxinsupp : x ∈ (Walk.cons hadj p).support := by
      rw [Walk.support_cons]; exact List.mem_cons_self
    have hxney : x ≠ y := by intro h; subst h; exact hxns (Walk.end_mem_support p)
    have hxiso : ∀ w, ¬ Hp.Adj x w := by
      intro w hadjw; rw [hHp, sup_adj] at hadjw
      rcases hadjw with h | h
      · exact hiso x hxinsupp hxney w h
      · rw [Subgraph.spanningCoe_adj] at h
        exact hxns (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert h))
    have hxz : x ≠ z := fun h => hxns (h ▸ Walk.start_mem_support p)
    have hnr : ¬ Hp.Reachable x z := by
      rintro ⟨wk⟩; cases wk with
      | nil => exact hxz rfl
      | cons hh _ => exact hxiso _ hh
    have hadjHp : ¬ Hp.Adj x z := fun h => hxiso z h
    have hface : faceCount (Hp ⊔ edge x z) = faceCount Hp :=
      faceCount_sup_edge_of_not_reachable Hp hxz hadjHp hnr
    refine ⟨?_, ?_⟩
    · rw [hunion, hface, hHp]; exact ihface
    · intro u hu
      rw [Walk.support_cons, List.mem_cons] at hu
      rw [hunion]
      have hle : Hp ≤ Hp ⊔ edge x z := le_sup_left
      have hxz_reach : (Hp ⊔ edge x z).Reachable x z :=
        Adj.reachable (by rw [sup_adj]; right; rw [edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, hxz⟩)
      rcases hu with rfl | hup
      · exact Reachable.refl _
      · exact hxz_reach.trans ((ihreach u hup).mono hle)


theorem jcx_faceCount_deleteCycle {V : Type*} [Finite V] [DecidableEq V]
    (K : SimpleGraph V) [LocallyFinite K] {v : V} (p : K.Walk v v) (hp : p.IsCycle)
    (hiso : ∀ u ∈ p.support, u ≠ v →
      ∀ w, ¬ (K.deleteEdges p.toSubgraph.edgeSet).Adj u w) :
    faceCount (K.deleteEdges p.toSubgraph.edgeSet) + 1 = faceCount K := by
  classical
  obtain ⟨z, hadj, q, hpeq, hqpath⟩ : ∃ (z : V) (hadj : K.Adj v z) (q : K.Walk z v),
      p = Walk.cons hadj q ∧ q.IsPath := by
    cases p with
    | nil => exact absurd Walk.nil_nil hp.not_nil
    | cons hadj q => rw [Walk.cons_isCycle_iff] at hp; exact ⟨_, hadj, q, rfl, hp.1⟩
  set K'' := K.deleteEdges p.toSubgraph.edgeSet with hK''
  have hqsub : ∀ u ∈ q.support, u ∈ p.support := by
    intro u hu; rw [hpeq, Walk.support_cons]; exact List.mem_cons_of_mem _ hu
  have hisoQ : ∀ u ∈ q.support, u ≠ v → ∀ w, ¬ K''.Adj u w :=
    fun u hu hne w => hiso u (hqsub u hu) hne w
  obtain ⟨hqface, hqreach⟩ := jcx_addWalk_faceCount q K'' hqpath hisoQ
  have hpspan : p.toSubgraph.spanningCoe = q.toSubgraph.spanningCoe ⊔ edge v z := by
    rw [hpeq]; exact jvp_consSpanningCoe hadj q
  have hKeq : K = K'' ⊔ p.toSubgraph.spanningCoe := by
    ext a b
    simp only [hK'', sup_adj, deleteEdges_adj, Subgraph.spanningCoe_adj]
    constructor
    · intro hKab
      by_cases hin : s(a, b) ∈ p.toSubgraph.edgeSet
      · right; rw [Subgraph.mem_edgeSet] at hin; exact hin
      · left; exact ⟨hKab, hin⟩
    · rintro (⟨hh, _⟩ | hh)
      · exact hh
      · exact p.toSubgraph.adj_sub hh
  set Kq := K'' ⊔ q.toSubgraph.spanningCoe with hKq
  have hKeq2 : K = Kq ⊔ edge v z := by rw [hKeq, hpspan, hKq]; ac_rfl
  have hzv : Kq.Reachable z v := by rw [hKq]; exact hqreach v (Walk.end_mem_support q)
  have hvz : Kq.Reachable v z := hzv.symm
  have hvzne : v ≠ z := K.ne_of_adj hadj
  have hvz_in_p : s(v, z) ∈ p.toSubgraph.edgeSet := by
    rw [hpeq]
    have : s(v, z) ∈ (Walk.cons hadj q).edges := by
      rw [Walk.edges_cons]; exact List.mem_cons_self
    rw [(Walk.cons hadj q).mem_edges_toSubgraph]; exact this
  have hvznadj : ¬ Kq.Adj v z := by
    rw [hKq, sup_adj]
    rintro (h | h)
    · rw [hK'', deleteEdges_adj] at h; exact h.2 hvz_in_p
    · rw [Subgraph.spanningCoe_adj, q.adj_toSubgraph_iff_mem_edges] at h
      have hpc : p.IsCycle := hp
      rw [hpeq, Walk.cons_isCycle_iff] at hpc
      exact hpc.2 (by rw [Sym2.eq_swap] at h ⊢; exact h)
  have hclose : faceCount (Kq ⊔ edge v z) = faceCount Kq + 1 :=
    faceCount_sup_edge_of_reachable Kq hvzne hvznadj hvz
  rw [hKeq2, hclose, hKq, hqface]


end Lattice
end StatMech
