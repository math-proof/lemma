/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalCoefficient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleExponent.Part2


namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising

theorem ons_finsuppAntidiag_finsetExponent_le
    {I E : Type*} [DecidableEq I] [DecidableEq E]
    (T : Finset I) (S : Finset E) (g : I →₀ E →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i : I} (hi : i ∈ T) (edge : E) :
    g i edge ≤ if edge ∈ S then 1 else 0 := by
  have hsum := (Finset.mem_finsuppAntidiag.mp hg).1
  have hle : g i edge ≤ (∑ j ∈ T, g j) edge := by
    rw [Finsupp.finsetSum_apply]
    exact Finset.single_le_sum
      (fun j _ ↦ Nat.zero_le (g j edge)) hi
  rw [hsum, ons_finsetExponent_apply] at hle
  exact hle

theorem ons_finsuppAntidiag_finsetExponent_component
    {I E : Type*} [DecidableEq I] [DecidableEq E]
    (T : Finset I) (S : Finset E) (g : I →₀ E →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i : I} (hi : i ∈ T) :
    g i = ons_finsetExponent (g i).support := by
  ext edge
  rw [ons_finsetExponent_apply]
  by_cases hedge : edge ∈ (g i).support
  · rw [if_pos hedge]
    have hpos : 0 < g i edge := Finsupp.mem_support_iff.mp hedge |> Nat.pos_of_ne_zero
    have hle := ons_finsuppAntidiag_finsetExponent_le T S g hg hi edge
    by_cases hedgeS : edge ∈ S
    · rw [if_pos hedgeS] at hle
      omega
    · rw [if_neg hedgeS] at hle
      omega
  · rw [if_neg hedge]
    exact Finsupp.notMem_support_iff.mp hedge

theorem ons_finsuppAntidiag_finsetExponent_support_subset
    {I E : Type*} [DecidableEq I] [DecidableEq E]
    (T : Finset I) (S : Finset E) (g : I →₀ E →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i : I} (hi : i ∈ T) :
    (g i).support ⊆ S := by
  intro edge hedge
  have hle := ons_finsuppAntidiag_finsetExponent_le T S g hg hi edge
  by_contra hedgeS
  rw [if_neg hedgeS] at hle
  have hpos : 0 < g i edge := Finsupp.mem_support_iff.mp hedge |> Nat.pos_of_ne_zero
  omega

theorem ons_finsuppAntidiag_finsetExponent_support_disjoint
    {I E : Type*} [DecidableEq I] [DecidableEq E]
    (T : Finset I) (S : Finset E) (g : I →₀ E →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i j : I} (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j) :
    Disjoint (g i).support (g j).support := by
  rw [Finset.disjoint_left]
  intro edge hei hej
  have hsum := (Finset.mem_finsuppAntidiag.mp hg).1
  have hiOne : g i edge = 1 := by
    rw [ons_finsuppAntidiag_finsetExponent_component T S g hg hi,
      ons_finsetExponent_apply, if_pos hei]
  have hjOne : g j edge = 1 := by
    rw [ons_finsuppAntidiag_finsetExponent_component T S g hg hj,
      ons_finsetExponent_apply, if_pos hej]
  have htwo : 2 ≤ (∑ k ∈ T, g k) edge := by
    rw [Finsupp.finsetSum_apply]
    calc
      2 = g i edge + g j edge := by rw [hiOne, hjOne]
      _ = ∑ k ∈ ({i, j} : Finset I), g k edge := by
        simp [hij]
      _ ≤ ∑ k ∈ T, g k edge :=
        Finset.sum_le_sum_of_subset (by
          intro k hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact hi
          · exact hj)
  rw [hsum, ons_finsetExponent_apply] at htwo
  split at htwo <;> omega

theorem ons_finsuppAntidiag_finsetExponent_support_cover
    {I E : Type*} [DecidableEq I] [DecidableEq E]
    (T : Finset I) (S : Finset E) (g : I →₀ E →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S)) :
    S = T.biUnion (fun i ↦ (g i).support) := by
  apply Finset.ext
  intro edge
  constructor
  · intro hedge
    rw [Finset.mem_biUnion]
    have hsum := congrArg (fun m : E →₀ ℕ ↦ m edge)
      (Finset.mem_finsuppAntidiag.mp hg).1
    have hsum' : ∑ i ∈ T, g i edge = 1 := by
      calc
        (∑ i ∈ T, g i edge) = (∑ i ∈ T, g i) edge :=
          (Finsupp.finsetSum_apply T (fun i ↦ g i) edge).symm
        _ = ons_finsetExponent S edge := hsum
        _ = 1 := by rw [ons_finsetExponent_apply, if_pos hedge]
    by_contra hnone
    push Not at hnone
    have hzero : ∑ i ∈ T, g i edge = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact Finsupp.notMem_support_iff.mp (hnone i hi)
    omega
  · intro hedge
    rw [Finset.mem_biUnion] at hedge
    obtain ⟨i, hi, hedge⟩ := hedge
    exact ons_finsuppAntidiag_finsetExponent_support_subset
      T S g hg hi hedge

theorem ons_decFormalLogCoeff_squarefree_cycle_of_ne_zero
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L))
    (hne : ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)
      (ons_finsetExponent S) ≠ 0) :
    ∃ (root : ons_Dart L)
      (q : (ons_decGraph L).Walk root root),
      q.IsCycle ∧ q.snd = ons_dartRev L root ∧
      q.edges.toFinset = S ∧
      ons_decFormalLogCoeff L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)
          (ons_finsetExponent S) =
        (ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) := by
  rcases ons_decFormalLogCoeff_squarefree_cases L a b S with hzero | hex
  · exact (hne hzero).elim
  · obtain ⟨r, d, hd, hcoeff⟩ := hex
    have hddata := (ons_mem_decSquarefreeLoopFinset L a b S d).mp hd
    let hvalid := ons_decLoop_valid_of_scalar_ne_zero L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) d hddata.2
    let q := ons_decLoopWalk L d hvalid
    have hq : q.IsCycle :=
      ons_decLoopWalk_isCycle_of_squarefree L d hvalid S hddata.1
    have hsnd : q.snd = ons_dartRev L (d 0) :=
      ons_decLoopWalk_snd L d hvalid
    have hedges : q.edges.toFinset = S :=
      ons_decLoopWalk_edges_toFinset_of_squarefree
        L d hvalid S hddata.1
    exact ⟨d 0, q, hq, hsnd, hedges, by
      simpa only [q, hvalid] using hcoeff⟩


theorem ons_isCycles_cycle_edges_eq_of_common_vertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hcyc : G.IsCycles) {u v : V}
    (p : G.Walk u u) (q : G.Walk v v)
    (hp : p.IsCycle) (hq : q.IsCycle)
    {x : V} (hxp : x ∈ p.toSubgraph.verts)
    (hxq : x ∈ q.toSubgraph.verts) :
    p.edges.toFinset = q.edges.toFinset := by
  have hpclosed : ∀ y ∈ p.toSubgraph.verts, ∀ z,
      G.Adj y z → p.toSubgraph.Adj y z := by
    intro y hy z hyz
    exact (hp.adj_toSubgraph_iff_of_isCycles hcyc hy z).mpr hyz
  have hqclosed : ∀ y ∈ q.toSubgraph.verts, ∀ z,
      G.Adj y z → q.toSubgraph.Adj y z := by
    intro y hy z hyz
    exact (hq.adj_toSubgraph_iff_of_isCycles hcyc hy z).mpr hyz
  obtain ⟨cp, hcp⟩ :=
    p.toSubgraph_connected.exists_verts_eq_connectedComponentSupp hpclosed
  obtain ⟨cq, hcq⟩ :=
    q.toSubgraph_connected.exists_verts_eq_connectedComponentSupp hqclosed
  have hxcp : x ∈ cp.supp := hcp ▸ hxp
  have hxcq : x ∈ cq.supp := hcq ▸ hxq
  have hc : cp = cq := by
    have hpRoot := (cp.mem_supp_iff x).mp hxcp
    have hqRoot := (cq.mem_supp_iff x).mp hxcq
    exact hpRoot.symm.trans hqRoot
  have hverts : p.toSubgraph.verts = q.toSubgraph.verts := by
    rw [hcp, hc, hcq]
  ext edge
  induction edge using Sym2.inductionOn with
  | _ y z =>
      simp only [List.mem_toFinset]
      rw [← p.mem_edges_toSubgraph, ← q.mem_edges_toSubgraph]
      constructor
      · intro hyz
        have hyq : y ∈ q.toSubgraph.verts := hverts ▸ hyz.fst_mem
        exact (hq.adj_toSubgraph_iff_of_isCycles hcyc hyq z).mpr
          hyz.adj_sub
      · intro hyz
        have hyp : y ∈ p.toSubgraph.verts := hverts.symm ▸ hyz.fst_mem
        exact (hp.adj_toSubgraph_iff_of_isCycles hcyc hyp z).mpr
          hyz.adj_sub

theorem ons_cycle_edges_eq_decomposition_piece
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ x, G.degree x ≤ 3)
    (S : Finset (Sym2 V)) (hS : S ∈ evenSubgraphs G)
    {I : Type*} [Fintype I] [DecidableEq I]
    (base : I → V) (p : (i : I) → G.Walk (base i) (base i))
    (hp : ∀ i, (p i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i ↦ (p i).edges.toFinset))
    {root : V} (q : G.Walk root root) (hq : q.IsCycle)
    (hqsub : q.edges.toFinset ⊆ S) :
    ∃ i : I, q.edges.toFinset = (p i).edges.toFinset := by
  let H := ons_edgeSubgraph S
  have hdata := hS
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  have hHedges : H.edgeSet = (S : Set (Sym2 V)) := by
    simpa [H] using ons_edgeSubgraph_edgeSet G S hdata.1
  have hHcycles : H.IsCycles := by
    simpa [H] using ons_isCycles_of_trivalent_even G hdeg S hS
  have hqNonempty : q.edges.toFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hedges : q.edges = [] :=
      (List.toFinset_eq_empty_iff q.edges).mp hempty
    exact hq.not_nil (SimpleGraph.Walk.edges_eq_nil.mp hedges)
  obtain ⟨edge, hedgeq⟩ := hqNonempty
  have hedgeS : edge ∈ S := hqsub hedgeq
  rw [hcover, Finset.mem_biUnion] at hedgeS
  obtain ⟨i, _, hedgei⟩ := hedgeS
  let qH : H.Walk root root := q.transfer H (by
    intro e he
    rw [hHedges]
    exact hqsub (List.mem_toFinset.mpr he))
  have hpiSub : (p i).edges.toFinset ⊆ S := by
    intro e he
    rw [hcover, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, he⟩
  let pH : H.Walk (base i) (base i) := (p i).transfer H (by
    intro e he
    rw [hHedges]
    exact hpiSub (List.mem_toFinset.mpr he))
  have hqH : qH.IsCycle := by
    exact hq.transfer _
  have hpH : pH.IsCycle := by
    exact (hp i).transfer _
  obtain ⟨x, y⟩ := edge
  have hedgeqList : s(x, y) ∈ q.edges := List.mem_toFinset.mp hedgeq
  have hedgeiList : s(x, y) ∈ (p i).edges := List.mem_toFinset.mp hedgei
  have hxq : x ∈ qH.toSubgraph.verts := by
    rw [SimpleGraph.Walk.mem_verts_toSubgraph]
    have hx : x ∈ q.support := q.fst_mem_support_of_mem_edges hedgeqList
    simpa [qH, SimpleGraph.Walk.support_transfer] using hx
  have hxp : x ∈ pH.toSubgraph.verts := by
    rw [SimpleGraph.Walk.mem_verts_toSubgraph]
    have hx : x ∈ (p i).support :=
      (p i).fst_mem_support_of_mem_edges hedgeiList
    simpa [pH, SimpleGraph.Walk.support_transfer] using hx
  have heq := ons_isCycles_cycle_edges_eq_of_common_vertex
    hHcycles qH pH hqH hpH hxq hxp
  refine ⟨i, ?_⟩
  calc
    q.edges.toFinset = qH.edges.toFinset := by
      rw [show qH.edges = q.edges from
        SimpleGraph.Walk.edges_transfer q _]
    _ = pH.edges.toFinset := heq
    _ = (p i).edges.toFinset := by
      rw [show pH.edges = (p i).edges from
        SimpleGraph.Walk.edges_transfer (p i) _]

theorem ons_decFormalLogCoeff_antidiag_component
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    (S : Finset (ons_DecEdge L))
    (hS : S ∈ evenSubgraphs (ons_decGraph L))
    {I : Type*} [Fintype I] [DecidableEq I]
    (base : I → ons_Dart L)
    (p : (i : I) → (ons_decGraph L).Walk (base i) (base i))
    (hp : ∀ i, (p i).IsCycle)
    (hcover : S = Finset.univ.biUnion
      (fun i ↦ (p i).edges.toFinset))
    {K : Type*} [DecidableEq K] (T : Finset K)
    (g : K →₀ ons_DecEdge L →₀ ℕ)
    (hg : g ∈ T.finsuppAntidiag (ons_finsetExponent S))
    {i : K} (hi : i ∈ T)
    (hne : ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) (g i) ≠ 0) :
    ∃ j : I,
      (g i).support = (p j).edges.toFinset ∧
      ons_decFormalLogCoeff L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) (g i) =
        (ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges (p j))) : ℂ) := by
  have hcomponent :=
    ons_finsuppAntidiag_finsetExponent_component T S g hg hi
  have hcoeffEq : ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) (g i) =
      ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)
        (ons_finsetExponent (g i).support) :=
    congrArg (ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)) hcomponent
  have hne' : ons_decFormalLogCoeff L ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)
      (ons_finsetExponent (g i).support) ≠ 0 := by
    intro hzero
    exact hne (hcoeffEq.trans hzero)
  obtain ⟨root, q, hq, hsnd, hqedges, hqcoeff⟩ :=
    ons_decFormalLogCoeff_squarefree_cycle_of_ne_zero
      L a b (g i).support hne'
  have hqsub : q.edges.toFinset ⊆ S := by
    rw [hqedges]
    exact ons_finsuppAntidiag_finsetExponent_support_subset
      T S g hg hi
  obtain ⟨j, hjedges⟩ := ons_cycle_edges_eq_decomposition_piece
    (ons_decGraph L) (ons_decGraph_degree_le_three L)
    S hS base p hp hcover q hq hqsub
  have hsupport : (g i).support = (p j).edges.toFinset := by
    rw [← hqedges, hjedges]
  have horiginal : ons_walkOriginalEdges q =
      ons_walkOriginalEdges (p j) :=
    ons_walkOriginalEdges_eq_of_edges_toFinset_eq q (p j) hjedges
  refine ⟨j, hsupport, ?_⟩
  calc
    ons_decFormalLogCoeff L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) (g i) =
        ons_decFormalLogCoeff L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)
          (ons_finsetExponent (g i).support) := hcoeffEq
    _ = (ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) := hqcoeff
    _ = (ons_spinCharacter a b
          (ons_evenHomology L
            (ons_walkOriginalEdges (p j))) : ℂ) := by rw [horiginal]

theorem ons_cycle_edges_toFinset_nonempty
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) :
    p.edges.toFinset.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hedges : p.edges = [] :=
    (List.toFinset_eq_empty_iff p.edges).mp hempty
  exact hp.not_nil (SimpleGraph.Walk.edges_eq_nil.mp hedges)

theorem ons_cycle_decomposition_edgeSet_injective
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} (base : I → V)
    (p : (i : I) → G.Walk (base i) (base i))
    (hp : ∀ i, (p i).IsCycle)
    (hdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i ↦ (p i).edges.toFinset)) :
    Function.Injective (fun i ↦ (p i).edges.toFinset) := by
  intro i j hij
  change (p i).edges.toFinset = (p j).edges.toFinset at hij
  by_contra hne
  have hd := hdisj (Finset.mem_univ i) (Finset.mem_univ j) hne
  change Disjoint (p i).edges.toFinset (p j).edges.toFinset at hd
  rw [hij] at hd
  have hempty : (p j).edges.toFinset = ∅ := disjoint_self.mp hd
  exact (ons_cycle_edges_toFinset_nonempty (p j) (hp j)).ne_empty hempty

end StatMech.Onsager
