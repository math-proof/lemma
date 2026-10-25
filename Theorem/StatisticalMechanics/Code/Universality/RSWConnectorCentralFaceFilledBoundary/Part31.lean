/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part27
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_exists_first_bookFlippedTraceIntersection {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ z : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'),
      ∀ q : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'),
        rlc_bookFlippedTraceIntersectionRank gamma gamma' z ≤
          rlc_bookFlippedTraceIntersectionRank gamma gamma' q := by
  classical
  have hne := rlc_bookFlippedTraceIntersectionSet_nonempty_of_faithful
    gamma gamma' hfaith
  letI : Nonempty ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma') :=
    ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have huniv : (Finset.univ :
      Finset ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma')).Nonempty :=
    ⟨⟨hne.choose, hne.choose_spec⟩, Finset.mem_univ _⟩
  obtain ⟨z, _hz, hmin⟩ := Finset.exists_min_image
    (Finset.univ :
      Finset ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'))
    (rlc_bookFlippedTraceIntersectionRank gamma gamma') huniv
  exact ⟨z, fun q => hmin q (by simp)⟩


theorem rlc_bookFirstFlippedTraceIntersection_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    let W := rlc_ambientCrossingWalk gamma.1
    ∃ (z : Site 2) (hzW : z ∈ W.support),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        (∀ q ∈ (W.takeUntil z hzW).support,
          rlc_flipX q ∈ rlc_pathVertices gamma'.1 → q = z) ∧
        ∀ q (hqW : q ∈ W.support),
          rlc_flipX q ∈ rlc_pathVertices gamma'.1 →
            (W.takeUntil z hzW).length ≤
              (W.takeUntil q hqW).length := by
  classical
  let W := rlc_ambientCrossingWalk gamma.1
  obtain ⟨zs, hmin⟩ :=
    rlc_exists_first_bookFlippedTraceIntersection gamma gamma' hfaith
  have hzMem := Finset.mem_filter.mp zs.2
  have hzRight : zs.1 ∈ rlc_pathVertices gamma.1 := hzMem.1
  have hzLeft : rlc_flipX zs.1 ∈ rlc_pathVertices gamma'.1 := hzMem.2
  have hzW : zs.1 ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 zs.1).2
      hzRight
  refine ⟨zs.1, hzW, hzRight, hzLeft, ?_, ?_⟩
  · intro q hqPrefix hqLeft
    by_contra hqz
    have hqW : q ∈ W.support :=
      W.support_takeUntil_subset_support hzW hqPrefix
    have hqRight : q ∈ rlc_pathVertices gamma.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hqW
    have hqSet : q ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma' := by
      simp [rlc_bookFlippedTraceIntersectionSet, hqRight, hqLeft]
    let qs : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma') :=
      ⟨q, hqSet⟩
    have hlen : (W.takeUntil q hqW).length <
        (W.takeUntil zs.1 hzW).length := by
      have h := (W.takeUntil zs.1 hzW).length_takeUntil_lt
        hqPrefix hqz
      rwa [W.takeUntil_takeUntil hzW hqPrefix] at h
    have hrankLt : rlc_bookFlippedTraceIntersectionRank gamma gamma' qs <
        rlc_bookFlippedTraceIntersectionRank gamma gamma' zs := by
      simpa [rlc_bookFlippedTraceIntersectionRank, W] using hlen
    exact (not_lt_of_ge (hmin qs)) hrankLt
  · intro q hqW hqLeft
    have hqRight : q ∈ rlc_pathVertices gamma.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).1 hqW
    have hqSet : q ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma' := by
      simp [rlc_bookFlippedTraceIntersectionSet, hqRight, hqLeft]
    let qs : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma') :=
      ⟨q, hqSet⟩
    simpa [rlc_bookFlippedTraceIntersectionRank, W] using hmin qs


theorem rlc_ambientCrossingWalk_isPath
    {a b c d : Int} (tau : RlcCrossingPath a b c d) :
    (rlc_ambientCrossingWalk tau).IsPath := by
  let hom : ((hypercubicLattice 2).induce (rect a b c d)) →g
      hypercubicLattice 2 :=
    (SimpleGraph.Embedding.induce (G := hypercubicLattice 2)
      (rect a b c d)).toHom
  let p : ((hypercubicLattice 2).induce (rect a b c d)).Walk _ _ :=
    tau.2.2.1
  change (p.map hom).IsPath
  apply p.map_isPath_of_injective
  · intro x y hxy
    exact Subtype.ext (by simpa [hom] using hxy)
  · exact (tau.2.2).2


theorem rlc_isPath_start_not_mem_tail {V : Type*} {G : SimpleGraph V}
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u ∉ p.support.tail := by
  have hnodup := hp.support_nodup
  rw [← SimpleGraph.Walk.cons_tail_support] at hnodup
  exact (List.nodup_cons.mp hnodup).1


theorem rlc_append_isPath_of_endpoint_intersection
    {V : Type*} {G : SimpleGraph V} {u v w : V}
    {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = v) :
    (p.append q).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
  refine List.Nodup.append hp.support_nodup
    ((List.tail_sublist _).nodup hq.support_nodup) ?_
  rw [List.disjoint_left]
  intro x hxp hxqTail
  have hxq : x ∈ q.support := List.tail_subset _ hxqTail
  have hxv := hinter x hxp hxq
  subst x
  exact rlc_isPath_start_not_mem_tail hq hxqTail


theorem rlc_append_isCycle_of_endpoint_intersection
    {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} {q : G.Walk v u}
    (hp : p.IsPath) (hq : q.IsPath) (huv : u ≠ v)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support →
      x = u ∨ x = v)
    (hedges : p.edges.Disjoint q.edges) :
    (p.append q).IsCycle := by
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def,
      SimpleGraph.Walk.edges_append]
    exact List.Nodup.append hp.edges_nodup hq.edges_nodup hedges
  · intro hnil
    have hlen : p.length + q.length = 0 := by
      rw [← SimpleGraph.Walk.length_append, hnil]
      rfl
    exact huv (SimpleGraph.Walk.eq_of_length_eq_zero
      (Nat.eq_zero_of_add_eq_zero_right hlen))
  · rw [SimpleGraph.Walk.tail_support_append]
    refine List.Nodup.append
      ((List.tail_sublist _).nodup hp.support_nodup)
      ((List.tail_sublist _).nodup hq.support_nodup) ?_
    rw [List.disjoint_left]
    intro x hxpTail hxqTail
    have hxp : x ∈ p.support := List.tail_subset _ hxpTail
    have hxq : x ∈ q.support := List.tail_subset _ hxqTail
    rcases hinter x hxp hxq with rfl | rfl
    · exact rlc_isPath_start_not_mem_tail hp hxpTail
    · exact rlc_isPath_start_not_mem_tail hq hxqTail

theorem rlc_cfct_vertexLoop_edges_mem_cycleFaceCut
    {a : Site 2} (c : (hypercubicLattice 2).Walk a a)
    (x : Site 2) (hx : x ∉ c.support) :
    ∀ e ∈ (jwc_vertexLoop (x 0) (x 1)).edges,
      e ∈ (whb_faceRegion c.toSubgraph.spanningCoe).edgeSet := by
  intro e he
  simp only [jwc_vertexLoop, SimpleGraph.Walk.edges_cons,
    SimpleGraph.Walk.edges_nil, List.mem_cons, List.not_mem_nil,
    or_false] at he
  have noCycleEdge {u v : Site 2} (huv : s(u, v) ∈ c.edges)
      (hxu : x = u ∨ x = v) : False := by
    rcases hxu with rfl | rfl
    · exact hx (c.fst_mem_support_of_mem_edges huv)
    · exact hx (c.snd_mem_support_of_mem_edges huv)
  rcases he with rfl | rfl | rfl | rfl
  · rw [SimpleGraph.mem_edgeSet, whb_faceRegion_adj]
    refine ⟨jwc_faceAdj_NE_NW _ _, ?_⟩
    rw [jwc_shared_NE_NW]
    intro hmem
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      c.mem_edges_toSubgraph] at hmem
    exact noCycleEdge hmem (Or.inl (cons_eq_site rfl rfl).symm)
  · rw [SimpleGraph.mem_edgeSet, whb_faceRegion_adj]
    refine ⟨jwc_faceAdj_NW_SW _ _, ?_⟩
    rw [jwc_shared_NW_SW]
    intro hmem
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      c.mem_edges_toSubgraph] at hmem
    exact noCycleEdge hmem (Or.inr (cons_eq_site rfl rfl).symm)
  · rw [SimpleGraph.mem_edgeSet, whb_faceRegion_adj]
    refine ⟨jwc_faceAdj_SW_SE _ _, ?_⟩
    rw [jwc_shared_SW_SE]
    intro hmem
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      c.mem_edges_toSubgraph] at hmem
    exact noCycleEdge hmem (Or.inr (cons_eq_site rfl rfl).symm)
  · rw [SimpleGraph.mem_edgeSet, whb_faceRegion_adj]
    refine ⟨jwc_faceAdj_SE_NE _ _, ?_⟩
    rw [jwc_shared_SE_NE]
    intro hmem
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      c.mem_edges_toSubgraph] at hmem
    exact noCycleEdge hmem (Or.inl (cons_eq_site rfl rfl).symm)


theorem rlc_cfct_cycleFaceCut_reachable_incidentFlanks_offSupport
    {a x y z h k : Site 2}
    (c : (hypercubicLattice 2).Walk a a)
    (hxy : (hypercubicLattice 2).Adj x y)
    (hxz : (hypercubicLattice 2).Adj x z)
    (hxoff : x ∉ c.support)
    (hh : h ∈ flankFaces x y) (hk : k ∈ flankFaces x z) :
    (whb_faceRegion c.toSubgraph.spanningCoe).Reachable h k := by
  let loop := jwc_vertexLoop (x 0) (x 1)
  let cutLoop := loop.transfer
    (whb_faceRegion c.toSubgraph.spanningCoe)
      (rlc_cfct_vertexLoop_edges_mem_cycleFaceCut c x hxoff)
  have hhLoop : h ∈ loop.support :=
    rlc_flank_mem_vertexLoop_support hxy hh
  have hkLoop : k ∈ loop.support :=
    rlc_flank_mem_vertexLoop_support hxz hk
  have hhCut : h ∈ cutLoop.support := by
    simpa [cutLoop, SimpleGraph.Walk.support_transfer] using hhLoop
  have hkCut : k ∈ cutLoop.support := by
    simpa [cutLoop, SimpleGraph.Walk.support_transfer] using hkLoop
  exact ⟨rlc_centralFaceContactSubwalk cutLoop hhCut hkCut⟩


theorem rlc_cfct_cycleFaceCut_reachable_flanks_of_not_cycleEdge
    {a x y h k : Site 2}
    (c : (hypercubicLattice 2).Walk a a)
    (hxy : (hypercubicLattice 2).Adj x y)
    (hnot : s(x, y) ∉ c.edges)
    (hh : h ∈ flankFaces x y) (hk : k ∈ flankFaces x y) :
    (whb_faceRegion c.toSubgraph.spanningCoe).Reachable h k := by
  obtain ⟨f, g, hflank, hfg⟩ := flankFaces_latAdj hxy
  have hshared : sharedPrimalEdge f g = s(x, y) := by
    calc
      sharedPrimalEdge f g = symPrimal f g :=
        (symPrimal_eq_shared hfg).symm
      _ = symPrimalSym s(f, g) := rfl
      _ = symPrimalSym (flankFaces x y) :=
        congrArg symPrimalSym hflank.symm
      _ = s(x, y) := symPrimalSym_flankFaces hxy
  have hfgCut : (whb_faceRegion c.toSubgraph.spanningCoe).Adj f g := by
    rw [whb_faceRegion_adj]
    refine ⟨hfg, ?_⟩
    rw [hshared]
    simpa [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      c.mem_edges_toSubgraph] using hnot
  rw [hflank, Sym2.mem_iff] at hh hk
  rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
  · exact Reachable.refl _
  · exact hfgCut.reachable
  · exact hfgCut.symm.reachable
  · exact Reachable.refl _


theorem rlc_cfct_cycleFaceCut_pathFlanks_reachable
    {a s t : Site 2}
    (c : (hypercubicLattice 2).Walk a a)
    (p : (hypercubicLattice 2).Walk s t)
    (hp : p.IsPath)
    (hoff : ∀ x ∈ p.support, x ≠ t → x ∉ c.support)
    (hedges : ∀ e ∈ p.edges, e ∉ c.edges)
    {f g : Site 2}
    (hf : ∃ x y : Site 2, s(x, y) ∈ p.edges ∧ f ∈ flankFaces x y)
    (hg : ∃ x y : Site 2, s(x, y) ∈ p.edges ∧ g ∈ flankFaces x y) :
    (whb_faceRegion c.toSubgraph.spanningCoe).Reachable f g := by
  induction p generalizing f g with
  | nil =>
      obtain ⟨x, y, hxy, _hf⟩ := hf
      simp at hxy
  | @cons u v w huv q ih =>
      have hqPath : q.IsPath := hp.of_cons
      have hqOff : ∀ x ∈ q.support, x ≠ w → x ∉ c.support := by
        intro x hx hxw
        apply hoff x
        · simp [SimpleGraph.Walk.support_cons, hx]
        · exact hxw
      have hqEdges : ∀ e ∈ q.edges, e ∉ c.edges := by
        intro e he
        exact hedges e (by simp [he])
      obtain ⟨xf, yf, hef, hff⟩ := hf
      obtain ⟨xg, yg, heg, hgg⟩ := hg
      rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hef heg
      have firstFlank {x y z : Site 2}
          (heq : s(x, y) = s(u, v)) (hz : z ∈ flankFaces x y) :
          z ∈ flankFaces u v := by
        have hm : flankFaces x y = flankFaces u v := by
          change flankFacesSym s(x, y) = flankFacesSym s(u, v)
          rw [heq]
        rwa [← hm]
      rcases hef with hef | hef <;> rcases heg with heg | heg
      · have hfFirst := firstFlank hef hff
        have hgFirst := firstFlank heg hgg
        apply rlc_cfct_cycleFaceCut_reachable_flanks_of_not_cycleEdge
          c huv (hedges _ (by simp)) hfFirst hgFirst
      · have hfFirst := firstFlank hef hff
        have hgTail : ∃ x y : Site 2,
            s(x, y) ∈ q.edges ∧ g ∈ flankFaces x y :=
          ⟨xg, yg, heg, hgg⟩
        have hqNotNil : ¬ q.Nil := by
          intro hnil
          have hqEdgesNil : q.edges = [] := by
            simpa [hnil.eq]
          have : s(xg, yg) ∈ ([] : List (Sym2 (Site 2))) :=
            hqEdgesNil ▸ heg
          simp at this
        have hvw : v ≠ w := by
          intro hvw
          apply rlc_isPath_start_not_mem_tail hqPath
          simpa [hvw] using q.end_mem_tail_support hqNotNil
        have hvOff : v ∉ c.support :=
          hoff v (by simp [SimpleGraph.Walk.support_cons]) hvw
        obtain ⟨k, l, hklFlank, hkl⟩ :=
          flankFaces_latAdj (q.adj_snd hqNotNil)
        have hk : k ∈ flankFaces v q.snd := by
          rw [hklFlank]
          exact Sym2.mem_mk_left _ _
        have hlocal :=
          rlc_cfct_cycleFaceCut_reachable_incidentFlanks_offSupport
            c huv.symm (q.adj_snd hqNotNil) hvOff
              (by simpa [flankFaces_comm] using hfFirst) hk
        have hkTail : ∃ x y : Site 2,
            s(x, y) ∈ q.edges ∧ k ∈ flankFaces x y :=
          ⟨v, q.snd, q.mk_start_snd_mem_edges hqNotNil, hk⟩
        exact hlocal.trans (ih hqPath hqOff hqEdges hkTail hgTail)
      · have hgFirst := firstFlank heg hgg
        have hfTail : ∃ x y : Site 2,
            s(x, y) ∈ q.edges ∧ f ∈ flankFaces x y :=
          ⟨xf, yf, hef, hff⟩
        have hqNotNil : ¬ q.Nil := by
          intro hnil
          have hqEdgesNil : q.edges = [] := by
            simpa [hnil.eq]
          have : s(xf, yf) ∈ ([] : List (Sym2 (Site 2))) :=
            hqEdgesNil ▸ hef
          simp at this
        have hvw : v ≠ w := by
          intro hvw
          apply rlc_isPath_start_not_mem_tail hqPath
          simpa [hvw] using q.end_mem_tail_support hqNotNil
        have hvOff : v ∉ c.support :=
          hoff v (by simp [SimpleGraph.Walk.support_cons]) hvw
        obtain ⟨k, l, hklFlank, hkl⟩ :=
          flankFaces_latAdj (q.adj_snd hqNotNil)
        have hk : k ∈ flankFaces v q.snd := by
          rw [hklFlank]
          exact Sym2.mem_mk_left _ _
        have hlocal :=
          rlc_cfct_cycleFaceCut_reachable_incidentFlanks_offSupport
            c huv.symm (q.adj_snd hqNotNil) hvOff
              (by simpa [flankFaces_comm] using hgFirst) hk
        have hkTail : ∃ x y : Site 2,
            s(x, y) ∈ q.edges ∧ k ∈ flankFaces x y :=
          ⟨v, q.snd, q.mk_start_snd_mem_edges hqNotNil, hk⟩
        exact (ih hqPath hqOff hqEdges hfTail hkTail).trans hlocal.symm
      · exact ih hqPath hqOff hqEdges
          ⟨xf, yf, hef, hff⟩ ⟨xg, yg, heg, hgg⟩


theorem rlc_cfct_faceInside_same_of_cycleFaceCut_reachable
    {a f g : Site 2}
    (c : (hypercubicLattice 2).Walk a a)
    (hcycle : c.IsCycle)
    (hreach : (whb_faceRegion c.toSubgraph.spanningCoe).Reachable f g) :
    fwr_faceInside c f ↔ fwr_faceInside c g := by
  obtain ⟨p⟩ := hreach
  induction p with
  | nil => exact Iff.rfl
  | @cons u v w huv q ih =>
      have huvData : (hypercubicLattice 2).Adj u v ∧
          sharedPrimalEdge u v ∉ c.toSubgraph.spanningCoe.edgeSet := by
        rwa [whb_faceRegion_adj] at huv
      have hnot : sharedPrimalEdge u v ∉ c.edges := by
        intro hc
        apply huvData.2
        rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
          c.mem_edges_toSubgraph]
        exact hc
      have hmatch := fwr_faceCutMatch_of_nodup
        c hcycle.edges_nodup huvData.1
      have hsame : fwr_faceInside c u ↔ fwr_faceInside c v := by
        have hnosplit : ¬ (fwr_faceInside c u ↔
            ¬ fwr_faceInside c v) := by
          intro hsplit
          exact hnot (hmatch.mp hsplit)
        tauto
      exact hsame.trans ih


theorem rlc_cfct_pathFlanks_outside_of_pinnedBoundaryFlank
    {a s t f₀ : Site 2}
    (c : (hypercubicLattice 2).Walk a a)
    (hcycle : c.IsCycle)
    (p : (hypercubicLattice 2).Walk s t)
    (hp : p.IsPath) (hpNotNil : ¬ p.Nil)
    (hoff : ∀ x ∈ p.support, x ≠ t → x ∉ c.support)
    (hedges : ∀ e ∈ p.edges, e ∉ c.edges)
    (hf₀ : f₀ ∈ flankFaces s p.snd)
    (hf₀Outside : phb_doubleDualEquiv.symm f₀ ∉ jec_leftRegion c) :
    ∀ {x y f : Site 2}, s(x, y) ∈ p.edges →
      f ∈ flankFaces x y →
      phb_doubleDualEquiv.symm f ∉ jec_leftRegion c := by
  intro x y f hxy hf
  have hf₀Witness : ∃ u v : Site 2,
      s(u, v) ∈ p.edges ∧ f₀ ∈ flankFaces u v :=
    ⟨s, p.snd, p.mk_start_snd_mem_edges hpNotNil, hf₀⟩
  have hfWitness : ∃ u v : Site 2,
      s(u, v) ∈ p.edges ∧ f ∈ flankFaces u v :=
    ⟨x, y, hxy, hf⟩
  have hreach := rlc_cfct_cycleFaceCut_pathFlanks_reachable
    c p hp hoff hedges hf₀Witness hfWitness
  have hsame := rlc_cfct_faceInside_same_of_cycleFaceCut_reachable
    c hcycle hreach
  have hf₀Face : ¬ fwr_faceInside c f₀ := by
    simpa [fwr_faceInside, phb_doubleDualEquiv,
      phb_doubleDualShift, jec_mem_leftRegion] using hf₀Outside
  have hfFace : ¬ fwr_faceInside c f := by
    exact fun hfIn => hf₀Face (hsame.mpr hfIn)
  simpa [fwr_faceInside, phb_doubleDualEquiv,
    phb_doubleDualShift, jec_mem_leftRegion] using hfFace


theorem rlc_cfct_rightBoundaryEdge_flank_outside_firstCycle
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {c : (hypercubicLattice 2).Walk
      (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)}
    (hcycle : c.IsCycle)
    (hedges : ∀ e ∈ c.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma')
    {x y f : Site 2}
    (hxRight : x 0 = 2 * n)
    (hxy : (hypercubicLattice 2).Adj x y)
    (hxoff : x ∉ c.support)
    (hf : f ∈ flankFaces x y) :
    phb_doubleDualEquiv.symm f ∉ jec_leftRegion c := by
  have hn : 0 ≤ n := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    have hs0 := gamma.1.1.2.2
    omega
  let up : Site 2 := ![x 0, x 1 + 1]
  let eastFace : Site 2 := ![x 0, x 1]
  have hxup : (hypercubicLattice 2).Adj x up := by
    simp [up, hypercubicLattice_adj, Fin.sum_univ_two]
  have heastFlank : eastFace ∈ flankFaces x up := by
    simp [eastFace, up, flankFaces]
  have hreach := rlc_cfct_cycleFaceCut_reachable_incidentFlanks_offSupport
    c hxup hxy hxoff heastFlank hf
  have hsame := rlc_cfct_faceInside_same_of_cycleFaceCut_reachable
    c hcycle hreach
  have hfar : ∀ p ∈ c.support,
      p 0 ≤ (phb_doubleDualEquiv.symm eastFace) 0 - 1 := by
    intro p hp
    have hpBound : p 0 ≤ 2 * n := by
      rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hp
      rcases hp with rfl | ⟨e, he, hpe⟩
      · have hs0 := gamma.1.1.2.2
        omega
      · have hpBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
          gamma gamma' (hedges e he) hpe
        have hpBox := rlc_connectorBarrier_mem_connectorBox
          gamma gamma' hpBarrier
        rw [mem_rect] at hpBox
        exact hpBox.2.1
    simpa [eastFace, phb_doubleDualEquiv, phb_doubleDualShift,
      hxRight] using hpBound
  have heastOutside : phb_doubleDualEquiv.symm eastFace ∉
      jec_leftRegion c := by
    rw [jec_mem_leftRegion, not_not]
    exact jec_ray_even_far c _ hfar
  have heastFace : ¬ fwr_faceInside c eastFace := by
    simpa [fwr_faceInside, phb_doubleDualEquiv,
      phb_doubleDualShift, jec_mem_leftRegion] using heastOutside
  have hfFace : ¬ fwr_faceInside c f := by
    exact fun hfIn => heastFace (hsame.mpr hfIn)
  simpa [fwr_faceInside, phb_doubleDualEquiv,
    phb_doubleDualShift, jec_mem_leftRegion] using hfFace


theorem rlc_cfct_rightBoundaryTail_flanks_outside_firstCycle
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {c : (hypercubicLattice 2).Walk
      (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)}
    (hcycle : c.IsCycle)
    (hcEdges : ∀ e ∈ c.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma')
    {x z : Site 2} (p : (hypercubicLattice 2).Walk x z)
    (hxRight : x 0 = 2 * n)
    (hp : p.IsPath) (hpNotNil : ¬ p.Nil)
    (hoff : ∀ w ∈ p.support, w ≠ z → w ∉ c.support)
    (hedges : ∀ e ∈ p.edges, e ∉ c.edges) :
    ∀ {u v f : Site 2}, s(u, v) ∈ p.edges →
      f ∈ flankFaces u v →
      phb_doubleDualEquiv.symm f ∉ jec_leftRegion c := by
  obtain ⟨f₀, g₀, hflank₀, _hfg₀⟩ :=
    flankFaces_latAdj (p.adj_snd hpNotNil)
  have hf₀ : f₀ ∈ flankFaces x p.snd := by
    rw [hflank₀]
    exact Sym2.mem_mk_left _ _
  have hxoff : x ∉ c.support := by
    apply hoff x p.start_mem_support
    intro hxz
    apply rlc_isPath_start_not_mem_tail hp
    simpa [hxz] using p.end_mem_tail_support hpNotNil
  have hf₀Outside := rlc_cfct_rightBoundaryEdge_flank_outside_firstCycle
    gamma gamma' hcycle hcEdges hxRight (p.adj_snd hpNotNil) hxoff hf₀
  intro u v f huv hf
  exact rlc_cfct_pathFlanks_outside_of_pinnedBoundaryFlank
    c hcycle p hp hpNotNil hoff hedges hf₀ hf₀Outside huv hf


theorem rlc_isPath_idxOf_le_of_mem_dropUntil
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b z q : V} (W : G.Walk a b) (hW : W.IsPath)
    (hz : z ∈ W.support) (hq : q ∈ (W.dropUntil z hz).support) :
    W.support.idxOf z ≤ W.support.idxOf q := by
  have hidxLt : W.support.idxOf z < W.support.length :=
    List.idxOf_lt_length_of_mem hz
  rw [SimpleGraph.Walk.dropUntil_eq_drop,
    SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.drop_support_eq_support_drop_min] at hq
  have hle : W.support.idxOf z ≤ W.length := by
    rw [SimpleGraph.Walk.length_support] at hidxLt
    omega
  rw [Nat.min_eq_left hle, List.mem_drop_iff_getElem] at hq
  obtain ⟨j, hj, hget⟩ := hq
  have hidxQ : W.support.idxOf q = W.support.idxOf z + j := by
    rw [← hget]
    simpa [Nat.add_comm] using hW.support_nodup.idxOf_getElem _ hj
  omega


theorem rlc_bookFirstIntersection_truncatedSides_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (z : Site 2)
      (right : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) z)
      (left : (hypercubicLattice 2).Walk
        (rlc_flipX z) (gamma'.1.2.1 : Site 2))
      (flipLeft : (hypercubicLattice 2).Walk
        z (gamma'.1.2.1 : Site 2))
      (preFlipLeft : (hypercubicLattice 2).Walk
        (rlc_flipX (gamma'.1.1 : Site 2)) z),
        z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        (∀ e ∈ right.edges, e ∈ rlc_pathEdges gamma.1) ∧
        (∀ e ∈ left.edges, e ∈ rlc_pathEdges gamma'.1) ∧
        (∀ e ∈ flipLeft.edges,
          e ∈ rlc_reflectedPathEdges gamma'.1) ∧
        (∀ x ∈ right.support, x ∈ flipLeft.support → x = z) ∧
        (∀ x : Site 2,
          x ∈ flipLeft.support ↔ rlc_flipX x ∈ left.support) ∧
        (∀ x ∈ flipLeft.support,
          (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX z) ≤
            (rlc_ambientCrossingWalk gamma'.1).support.idxOf
              (rlc_flipX x)) ∧
        (∀ x ∈ preFlipLeft.support,
          x ∈ right.support → x = z) ∧
        (∀ x ∈ preFlipLeft.support,
          x ∈ flipLeft.support → x = z) ∧
        (∀ x ∈ preFlipLeft.support, x ≠ z → 0 < x 0) ∧
        right.IsPath ∧ left.IsPath ∧ flipLeft.IsPath ∧
        preFlipLeft.IsPath ∧
        (∀ e ∈ ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).edges,
          e ∈ preFlipLeft.edges ∨ e ∈ flipLeft.edges) ∧
        (right.append flipLeft).IsPath ∧
        right.length =
          (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧
        ∀ q (hq : q ∈ rlc_pathVertices gamma.1),
          rlc_flipX q ∈ rlc_pathVertices gamma'.1 →
            right.length ≤
              (rlc_ambientCrossingWalk gamma.1).support.idxOf q := by
  classical
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  obtain ⟨z, hzWR, hzRight, hzLeft, hfirst, hglobalMin⟩ :=
    rlc_bookFirstFlippedTraceIntersection_of_faithful
      gamma gamma' hfaith
  have hzWL : rlc_flipX z ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX z)).2 hzLeft
  let right : (hypercubicLattice 2).Walk
      (gamma.1.1 : Site 2) z := WR.takeUntil z hzWR
  let left : (hypercubicLattice 2).Walk
      (rlc_flipX z) (gamma'.1.2.1 : Site 2) :=
    WL.dropUntil (rlc_flipX z) hzWL
  let preLeft : (hypercubicLattice 2).Walk
      (gamma'.1.1 : Site 2) (rlc_flipX z) :=
    WL.takeUntil (rlc_flipX z) hzWL
  have hflipUpper : rlc_flipX (gamma'.1.2.1 : Site 2) =
      (gamma'.1.2.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  let flipLeft : (hypercubicLattice 2).Walk
      z (gamma'.1.2.1 : Site 2) :=
    (left.map rlc_flipXLatticeHom).copy
      (rlc_flipX_involutive z) hflipUpper
  let preFlipLeft : (hypercubicLattice 2).Walk
      (rlc_flipX (gamma'.1.1 : Site 2)) z :=
    (preLeft.map rlc_flipXLatticeHom).copy rfl
      (rlc_flipX_involutive z)
  have hrightPath : right.IsPath :=
    (rlc_ambientCrossingWalk_isPath gamma.1).takeUntil hzWR
  have hleftPath : left.IsPath :=
    (rlc_ambientCrossingWalk_isPath gamma'.1).dropUntil hzWL
  have hpreLeftPath : preLeft.IsPath :=
    (rlc_ambientCrossingWalk_isPath gamma'.1).takeUntil hzWL
  have hflipLeftPath : flipLeft.IsPath := by
    dsimp only [flipLeft]
    rw [SimpleGraph.Walk.isPath_copy]
    apply left.map_isPath_of_injective
    · exact rlc_flipX.injective
    · exact hleftPath
  have hpreFlipLeftPath : preFlipLeft.IsPath := by
    dsimp only [preFlipLeft]
    rw [SimpleGraph.Walk.isPath_copy]
    apply preLeft.map_isPath_of_injective
    · exact rlc_flipX.injective
    · exact hpreLeftPath
  have hinter : ∀ x ∈ right.support,
      x ∈ flipLeft.support → x = z := by
    intro x hxRight hxFlipLeft
    have hxWR : x ∈ (WR.takeUntil z hzWR).support := by
      simpa [right] using hxRight
    have hxMapped : x ∈ (left.map rlc_flipXLatticeHom).support := by
      simpa [flipLeft] using hxFlipLeft
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hxMapped
    obtain ⟨y, hyLeft, hyx⟩ := hxMapped
    change rlc_flipX y = x at hyx
    have hyWL : y ∈ WL.support :=
      WL.support_dropUntil_subset hzWL hyLeft
    have hyPath : y ∈ rlc_pathVertices gamma'.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 y).1
        hyWL
    have hflipX : rlc_flipX x = y := by
      rw [← hyx]
      simp
    exact hfirst x hxWR (by simpa [hflipX] using hyPath)
  have hflipLeftSupport (x : Site 2) :
      x ∈ flipLeft.support ↔ rlc_flipX x ∈ left.support := by
    dsimp only [flipLeft]
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change rlc_flipX (rlc_flipX y) ∈ left.support
      simpa using hy
    · intro hx
      exact ⟨rlc_flipX x, hx, rlc_flipX_involutive x⟩
  have hflipLeftRank : ∀ x ∈ flipLeft.support,
      WL.support.idxOf (rlc_flipX z) ≤
        WL.support.idxOf (rlc_flipX x) := by
    intro x hx
    apply rlc_isPath_idxOf_le_of_mem_dropUntil WL
      (rlc_ambientCrossingWalk_isPath gamma'.1) hzWL
    exact hflipLeftSupport x |>.1 hx
  have hpreFlipLeftSupport (x : Site 2) :
      x ∈ preFlipLeft.support ↔ rlc_flipX x ∈ preLeft.support := by
    dsimp only [preFlipLeft]
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change rlc_flipX (rlc_flipX y) ∈ preLeft.support
      simpa using hy
    · intro hx
      exact ⟨rlc_flipX x, hx, rlc_flipX_involutive x⟩
  have hpreRightInter : ∀ x ∈ preFlipLeft.support,
      x ∈ right.support → x = z := by
    intro x hxPre hxRight
    have hflipPre : rlc_flipX x ∈ preLeft.support :=
      (hpreFlipLeftSupport x).1 hxPre
    have hflipWL : rlc_flipX x ∈ WL.support :=
      WL.support_takeUntil_subset_support hzWL hflipPre
    have hflipPath : rlc_flipX x ∈ rlc_pathVertices gamma'.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 (rlc_flipX x)).1 hflipWL
    have hxWR : x ∈ (WR.takeUntil z hzWR).support := by
      simpa [right] using hxRight
    exact hfirst x hxWR hflipPath
  have hpreSuffixRaw : ∀ y ∈ preLeft.support,
      y ∈ left.support → y = rlc_flipX z := by
    intro y hyPre hyLeft
    by_contra hyq
    have hwhole : (preLeft.append left).IsPath := by
      have hWPath := rlc_ambientCrossingWalk_isPath gamma'.1
      simpa [preLeft, left] using hWPath
    exact (hwhole.ne_of_mem_support_of_append hyq hyPre hyLeft) rfl
  have hpreSuffixInter : ∀ x ∈ preFlipLeft.support,
      x ∈ flipLeft.support → x = z := by
    intro x hxPre hxSuffix
    have hxPre' := (hpreFlipLeftSupport x).1 hxPre
    have hxSuffix' := (hflipLeftSupport x).1 hxSuffix
    have hxEq := hpreSuffixRaw _ hxPre' hxSuffix'
    apply rlc_flipX.injective
    simpa using hxEq
  have hprePositive : ∀ x ∈ preFlipLeft.support,
      x ≠ z → 0 < x 0 := by
    intro x hxPre hxz
    have hxPre' := (hpreFlipLeftSupport x).1 hxPre
    have hxWL : rlc_flipX x ∈ WL.support :=
      WL.support_takeUntil_subset_support hzWL hxPre'
    have hxPath : rlc_flipX x ∈ rlc_pathVertices gamma'.1 :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 (rlc_flipX x)).1 hxWL
    have hxNeEnd : rlc_flipX x ≠ (gamma'.1.2.1 : Site 2) := by
      intro hxEnd
      have hEndLeft : (gamma'.1.2.1 : Site 2) ∈ left.support :=
        left.end_mem_support
      have hxJoin := hpreSuffixRaw _ hxPre' (by simpa [hxEnd] using hEndLeft)
      apply hxz
      apply rlc_flipX.injective
      simpa [hxEnd] using hxJoin
    have hxNeg := hfaith.left_vertex_strict hxPath hxNeEnd
    change -x 0 < 0 at hxNeg
    omega
  have hflipLeftEdges : ∀ e ∈ flipLeft.edges,
      e ∈ rlc_reflectedPathEdges gamma'.1 := by
    intro e he
    dsimp only [flipLeft] at he
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    rw [rlc_reflectedPathEdges, Finset.mem_image]
    refine ⟨e0, ?_, rfl⟩
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma'.1
    exact WL.edges_dropUntil_subset hzWL he0
  refine ⟨z, right, left, flipLeft, preFlipLeft,
    hzRight, hzLeft, ?_, ?_, hflipLeftEdges, hinter,
    hflipLeftSupport, hflipLeftRank, hpreRightInter, hpreSuffixInter,
    hprePositive, hrightPath, hleftPath, hflipLeftPath,
    hpreFlipLeftPath, ?_, ?_, ?_, ?_⟩
  · intro e he
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma.1
    exact WR.edges_takeUntil_subset hzWR he
  · intro e he
    apply rlc_ambientCrossingWalk_edge_mem_pathEdges gamma'.1
    exact WL.edges_dropUntil_subset hzWL he
  · intro e he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    change e0 ∈ WL.edges at he0
    have htake := SimpleGraph.Walk.take_spec WL hzWL
    rw [← htake, SimpleGraph.Walk.edges_append,
      List.mem_append] at he0
    rcases he0 with hePre | heSuffix
    · left
      dsimp only [preFlipLeft]
      rw [SimpleGraph.Walk.edges_copy,
        SimpleGraph.Walk.edges_map, List.mem_map]
      exact ⟨e0, hePre, rfl⟩
    · right
      dsimp only [flipLeft]
      rw [SimpleGraph.Walk.edges_copy,
        SimpleGraph.Walk.edges_map, List.mem_map]
      exact ⟨e0, heSuffix, rfl⟩
  · exact rlc_append_isPath_of_endpoint_intersection
      hrightPath hflipLeftPath hinter
  · simp [right, WR, SimpleGraph.Walk.length_takeUntil]
  · intro q hq hqLeft
    have hqWR :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 q).2 hq
    simpa [right, WR, SimpleGraph.Walk.length_takeUntil] using
      hglobalMin q hqWR hqLeft

set_option maxHeartbeats 2000000 in


theorem rlc_bookFirstIntersectionFourTraceAxisCycle_of_faithful {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (c : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)),
      c.IsCycle ∧
        (gamma.1.1 : Site 2) ∈ c.support ∧
        (gamma'.1.2.1 : Site 2) ∈ c.support ∧
        (∀ e ∈ c.edges,
          e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧
        (∀ k : Int,
          (gamma.1.1 : Site 2) 1 < k →
          k ≤ (gamma'.1.2.1 : Site 2) 1 →
          ¬ Even (jec_rayCount (![1, k] : Site 2) c)) ∧
        ∀ {x y : Site 2},
          s(x, y) ∈ ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).edges →
          s(x, y) ∈ c.edges ∨
            ∀ h ∈ flankFaces x y,
              phb_doubleDualEquiv.symm h ∉ jec_leftRegion c := by
  obtain ⟨z, right, left, flipLeft, preFlipLeft, hzRight, hzLeft,
    hrightEdges, hleftEdges, hflipLeftEdges, hinter, hflipLeftSupport,
    _hflipLeftRank, hpreRightInter, hpreSuffixInter, hprePositive,
    hrightPath, hleftPath, _hflipLeftPath, hpreFlipLeftPath,
    hleftMappedSplit, hrightHalfPath, _hrankRealized, _hglobalMin⟩ :=
      rlc_bookFirstIntersection_truncatedSides_of_faithful
        gamma gamma' hfaith
  let q := rlc_flipX z
  have hflipLower : rlc_flipX (gamma.1.1 : Site 2) =
      (gamma.1.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  let flipRightRev : (hypercubicLattice 2).Walk
      q (gamma.1.1 : Site 2) :=
    (right.map rlc_flipXLatticeHom).reverse.copy rfl hflipLower
  let rightHalf := right.append flipLeft
  let leftHalf := left.reverse.append flipRightRev
  let c := rightHalf.append leftHalf
  have hflipRightPath : flipRightRev.IsPath := by
    dsimp only [flipRightRev]
    rw [SimpleGraph.Walk.isPath_copy,
      SimpleGraph.Walk.isPath_reverse_iff]
    apply right.map_isPath_of_injective
    · exact rlc_flipX.injective
    · exact hrightPath
  have hleftFlipInter : ∀ x ∈ left.reverse.support,
      x ∈ flipRightRev.support → x = q := by
    intro x hxLeftRev hxFlipRight
    have hxLeft : x ∈ left.support := by
      simpa [SimpleGraph.Walk.support_reverse] using hxLeftRev
    dsimp only [flipRightRev] at hxFlipRight
    rw [SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_reverse, List.mem_reverse,
      SimpleGraph.Walk.support_map, List.mem_map] at hxFlipRight
    obtain ⟨y, hyRight, hyx⟩ := hxFlipRight
    change rlc_flipX y = x at hyx
    have hyFlipLeft : y ∈ flipLeft.support :=
      (hflipLeftSupport y).2 (by simpa [hyx] using hxLeft)
    have hyz := hinter y hyRight hyFlipLeft
    subst y
    simpa [q] using hyx.symm
  have hleftHalfPath : leftHalf.IsPath := by
    exact rlc_append_isPath_of_endpoint_intersection
      hleftPath.reverse hflipRightPath hleftFlipInter
  have hflipRightEdges : ∀ e ∈ flipRightRev.edges,
      e ∈ rlc_reflectedPathEdges gamma.1 := by
    intro e he
    dsimp only [flipRightRev] at he
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_reverse,
      List.mem_reverse, SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    rw [rlc_reflectedPathEdges, Finset.mem_image]
    exact ⟨e0, hrightEdges e0 he0, rfl⟩
  have hrightHalfFour : ∀ e ∈ rightHalf.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    change e ∈ (right.append flipLeft).edges at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges]
    rcases he with he | he
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (hrightEdges e he))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (hflipLeftEdges e he))
  have hleftHalfFour : ∀ e ∈ leftHalf.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    change e ∈ (left.reverse.append flipRightRev).edges at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append,
      SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
    rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges]
    rcases he with he | he
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (hleftEdges e he))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (hflipRightEdges e he))
  have hrightSupport : ∀ x ∈ right.support,
      x ∈ rlc_pathVertices gamma.1 := by
    intro x hx
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hx
    rcases hx with rfl | ⟨e, he, hxe⟩
    · exact hzRight
    · induction e using Sym2.inductionOn with
      | _ a b =>
          have hab := rlc_pathEdge_endpoints_mem_vertices gamma.1
            (hrightEdges s(a, b) he)
          rw [Sym2.mem_iff] at hxe
          exact hxe.elim (fun h ↦ h ▸ hab.1) (fun h ↦ h ▸ hab.2)
  have hleftSupport : ∀ x ∈ left.support,
      x ∈ rlc_pathVertices gamma'.1 := by
    intro x hx
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hx
    rcases hx with rfl | ⟨e, he, hxe⟩
    · exact rlc_connector_path_end_mem_vertices gamma'.1
    · induction e using Sym2.inductionOn with
      | _ a b =>
          have hab := rlc_pathEdge_endpoints_mem_vertices gamma'.1
            (hleftEdges s(a, b) he)
          rw [Sym2.mem_iff] at hxe
          exact hxe.elim (fun h ↦ h ▸ hab.1) (fun h ↦ h ▸ hab.2)
  have hrightHalfNonneg : ∀ x ∈ rightHalf.support, 0 ≤ x 0 := by
    intro x hx
    change x ∈ (right.append flipLeft).support at hx
    rw [SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · have hrect := rlc_pathVertex_mem_rect gamma.1
        (hrightSupport x hx)
      rw [mem_rect] at hrect
      exact hrect.1
    · have hrect := rlc_pathVertex_mem_rect gamma'.1
        (hleftSupport _ ((hflipLeftSupport x).1 hx))
      rw [mem_rect] at hrect
      have hxBound := hrect.2.1
      change -(x 0) ≤ 0 at hxBound
      omega
  have hleftHalfNonpos : ∀ x ∈ leftHalf.support, x 0 ≤ 0 := by
    intro x hx
    change x ∈ (left.reverse.append flipRightRev).support at hx
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse, List.mem_reverse] at hx
    rcases hx with hx | hx
    · have hrect := rlc_pathVertex_mem_rect gamma'.1
        (hleftSupport x hx)
      rw [mem_rect] at hrect
      exact hrect.2.1
    · dsimp only [flipRightRev] at hx
      rw [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_reverse, List.mem_reverse,
        SimpleGraph.Walk.support_map, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hrect := rlc_pathVertex_mem_rect gamma.1
        (hrightSupport y hy)
      rw [mem_rect] at hrect
      change -y 0 ≤ 0
      omega
  have hrightHalfAxis : ∀ x ∈ rightHalf.support, x 0 = 0 →
      x = (gamma.1.1 : Site 2) ∨ x = (gamma'.1.2.1 : Site 2) := by
    intro x hx hx0
    change x ∈ (right.append flipLeft).support at hx
    rw [SimpleGraph.Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · exact Or.inl (hfaith.right_axis_unique
        (hrightSupport x hx) hx0)
    · right
      have hxLeft := hleftSupport _ ((hflipLeftSupport x).1 hx)
      have hflip0 : (rlc_flipX x) 0 = 0 := by
        change -(x 0) = 0
        omega
      have hleftEnd := hfaith.left_axis_unique hxLeft hflip0
      have hself := rlc_flipX_eq_self_of_zero hx0
      rwa [hself] at hleftEnd
  have hhalvesInter : ∀ x, x ∈ rightHalf.support →
      x ∈ leftHalf.support →
      x = (gamma.1.1 : Site 2) ∨ x = (gamma'.1.2.1 : Site 2) := by
    intro x hxRight hxLeft
    have hx0 : x 0 = 0 := by
      have hr := hrightHalfNonneg x hxRight
      have hl := hleftHalfNonpos x hxLeft
      omega
    exact hrightHalfAxis x hxRight hx0
  have hhalfEdges : rightHalf.edges.Disjoint leftHalf.edges := by
    rw [List.disjoint_left]
    intro e heRight heLeft
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hx := hhalvesInter x
          (rightHalf.fst_mem_support_of_mem_edges heRight)
          (leftHalf.fst_mem_support_of_mem_edges heLeft)
        have hy := hhalvesInter y
          (rightHalf.snd_mem_support_of_mem_edges heRight)
          (leftHalf.snd_mem_support_of_mem_edges heLeft)
        have hxy := rightHalf.adj_of_mem_edges heRight
        have hedge : s(x, y) =
            s((gamma.1.1 : Site 2), (gamma'.1.2.1 : Site 2)) := by
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exact False.elim (hxy.ne rfl)
          · rfl
          · exact Sym2.eq_swap
          · exact False.elim (hxy.ne rfl)
        have horder := hfaith.axis_contacts_strict
        have hstep : (gamma'.1.2.1 : Site 2) 1 =
            (gamma.1.1 : Site 2) 1 + 1 := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two] at hxy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
            simp_all <;> omega
        have haxisEdge :
            s((gamma.1.1 : Site 2), (gamma'.1.2.1 : Site 2)) =
              s((![0, (gamma'.1.2.1 : Site 2) 1 - 1] : Site 2),
                ![0, (gamma'.1.2.1 : Site 2) 1]) := by
          rw [Sym2.eq_iff]
          left
          constructor <;> ext i <;> fin_cases i <;>
            simp [gamma.1.1.2.2, gamma'.1.2.1.2.2] <;> omega
        apply rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
          gamma gamma' hfaith ((gamma'.1.2.1 : Site 2) 1)
        rw [← haxisEdge, ← hedge]
        exact hrightHalfFour s(x, y) heRight
  have hcycle : c.IsCycle := by
    have hcontactsNe : (gamma.1.1 : Site 2) ≠
        (gamma'.1.2.1 : Site 2) := by
      intro h
      have hrow := congrArg (fun x : Site 2 => x 1) h
      exact (ne_of_lt hfaith.axis_contacts_strict) hrow
    exact rlc_append_isCycle_of_endpoint_intersection
      hrightHalfPath hleftHalfPath
        hcontactsNe hhalvesInter hhalfEdges
  have hcFour : ∀ e ∈ c.edges,
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    dsimp only [c] at he
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    exact he.elim (hrightHalfFour e) (hleftHalfFour e)
  have hpreOff : ∀ x ∈ preFlipLeft.support,
      x ≠ z → x ∉ c.support := by
    intro x hxPre hxz hxc
    change x ∈ (rightHalf.append leftHalf).support at hxc
    rw [SimpleGraph.Walk.mem_support_append_iff] at hxc
    rcases hxc with hxRightHalf | hxLeftHalf
    · change x ∈ (right.append flipLeft).support at hxRightHalf
      rw [SimpleGraph.Walk.mem_support_append_iff] at hxRightHalf
      rcases hxRightHalf with hxRight | hxSuffix
      · exact hxz (hpreRightInter x hxPre hxRight)
      · exact hxz (hpreSuffixInter x hxPre hxSuffix)
    · have hxPos := hprePositive x hxPre hxz
      have hxNonpos := hleftHalfNonpos x hxLeftHalf
      omega
  have hpreEdges : ∀ e ∈ preFlipLeft.edges, e ∉ c.edges := by
    intro e hePre heCycle
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy := preFlipLeft.adj_of_mem_edges hePre
        have hxPre := preFlipLeft.fst_mem_support_of_mem_edges hePre
        have hyPre := preFlipLeft.snd_mem_support_of_mem_edges hePre
        have hxCycle := c.fst_mem_support_of_mem_edges heCycle
        have hyCycle := c.snd_mem_support_of_mem_edges heCycle
        by_cases hxz : x = z
        · have hyz : y ≠ z := by
            intro hyz
            exact hxy.ne (hxz.trans hyz.symm)
          exact hpreOff y hyPre hyz hyCycle
        · exact hpreOff x hxPre hxz hxCycle
  have hpreStartRight :
      (rlc_flipX (gamma'.1.1 : Site 2)) 0 = 2 * n := by
    change -(gamma'.1.1 : Site 2) 0 = 2 * n
    rw [gamma'.1.1.2.2]
    ring
  have hpreExterior {x y h : Site 2}
      (hxy : s(x, y) ∈ preFlipLeft.edges)
      (hh : h ∈ flankFaces x y) :
      phb_doubleDualEquiv.symm h ∉ jec_leftRegion c := by
    have hpreNotNil : ¬ preFlipLeft.Nil := by
      intro hnil
      have hnilEdges : preFlipLeft.edges = [] := by
        simpa [hnil.eq]
      have : s(x, y) ∈ ([] : List (Sym2 (Site 2))) :=
        hnilEdges ▸ hxy
      simp at this
    exact rlc_cfct_rightBoundaryTail_flanks_outside_firstCycle
      gamma gamma' hcycle hcFour preFlipLeft hpreStartRight
        hpreFlipLeftPath hpreNotNil hpreOff hpreEdges hxy hh
  have hleftMappedCover {x y : Site 2}
      (hxy : s(x, y) ∈ ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).edges) :
      s(x, y) ∈ c.edges ∨
        ∀ h ∈ flankFaces x y,
          phb_doubleDualEquiv.symm h ∉ jec_leftRegion c := by
    rcases hleftMappedSplit s(x, y) hxy with hePre | heSuffix
    · right
      intro h hh
      apply hpreExterior (x := x) (y := y)
      · exact hePre
      · exact hh
    · left
      have hrightHalf : s(x, y) ∈
          rightHalf.edges := by
        change s(x, y) ∈
          (right.append flipLeft).edges
        rw [SimpleGraph.Walk.edges_append, List.mem_append]
        exact Or.inr heSuffix
      change s(x, y) ∈ (rightHalf.append leftHalf).edges
      rw [SimpleGraph.Walk.edges_append, List.mem_append]
      exact Or.inl hrightHalf
  refine ⟨c, hcycle, c.start_mem_support, ?_, hcFour, ?_, ?_⟩
  · dsimp only [c]
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl rightHalf.end_mem_support
  · intro k hkLower hkUpper
    have hrightRay : jec_rayCount (![1, k] : Site 2) rightHalf = 0 := by
      rw [jec_rayCount, List.countP_eq_zero]
      intro e he
      simp only [decide_eq_true_eq]
      intro hray
      induction e using Sym2.inductionOn with
      | _ u v =>
          have hu0 := hrightHalfNonneg u
            (rightHalf.fst_mem_support_of_mem_edges he)
          have hv0 := hrightHalfNonneg v
            (rightHalf.snd_mem_support_of_mem_edges he)
          have hfour := hrightHalfFour s(u, v) he
          rw [jec_rayEdge_mk] at hray
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hray
          rcases hray with ⟨⟨huv0, hcol⟩,
              ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩⟩
          · have huEq : u = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            rw [huEq, hvEq] at hfour
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k hfour
          · have huEq : u = (![0, k] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            have hvEq : v = (![0, k - 1] : Site 2) := by
              ext i
              fin_cases i <;> simp <;> omega
            rw [huEq, hvEq] at hfour
            exact rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
              gamma gamma' hfaith k (by
                simpa [Sym2.eq_swap] using hfour)
    have hleftRay : jec_rayCount (![1, k] : Site 2) leftHalf =
        crossCount (jec_belowSet k) leftHalf := by
      apply jec_ray_eq_below
      intro x hx
      simpa using hleftHalfNonpos x hx
    have hleftOdd :
        ¬ Even (jec_rayCount (![1, k] : Site 2) leftHalf) := by
      rw [hleftRay]
      intro heven
      have hsame := (crossCount_parity (jec_belowSet k) leftHalf).mp heven
      have hupperNot :
          (gamma'.1.2.1 : Site 2) ∉ jec_belowSet k := by
        simp [jec_belowSet]
        omega
      have hlowerIn : (gamma.1.1 : Site 2) ∈ jec_belowSet k := by
        simp [jec_belowSet]
        omega
      exact hupperNot (hsame.mpr hlowerIn)
    change ¬ Even (jec_rayCount (![1, k] : Site 2)
      (rightHalf.append leftHalf))
    rw [jec_rayCount_append, hrightRay, zero_add]
    exact hleftOdd
  · intro x y hxy
    exact hleftMappedCover hxy


theorem rlc_cycleEdge_oppositeFlank_outside
    {a x y h k : Site 2}
    {c : (hypercubicLattice 2).Walk a a}
    (hcycle : c.IsCycle)
    (hxy : (hypercubicLattice 2).Adj x y)
    (hflank : flankFaces x y = s(h, k))
    (hedge : s(x, y) ∈ c.edges)
    (hhInside : phb_doubleDualEquiv.symm h ∈ jec_leftRegion c) :
    phb_doubleDualEquiv.symm k ∉ jec_leftRegion c := by
  obtain ⟨f, g, hfgFlank, hfgAdj⟩ := flankFaces_latAdj hxy
  have hhk : s(h, k) = s(f, g) := hflank.symm.trans hfgFlank
  have hhkAdj : (hypercubicLattice 2).Adj h k := by
    rw [Sym2.eq_iff] at hhk
    rcases hhk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hfgAdj
    · exact hfgAdj.symm
  have hshared : sharedPrimalEdge h k = s(x, y) := by
    calc
      sharedPrimalEdge h k = symPrimal h k :=
        (symPrimal_eq_shared hhkAdj).symm
      _ = symPrimalSym s(h, k) := rfl
      _ = symPrimalSym (flankFaces x y) :=
        congrArg symPrimalSym hflank.symm
      _ = s(x, y) := symPrimalSym_flankFaces hxy
  have hsplit := (fwr_faceCutMatch_of_nodup
    c hcycle.edges_nodup hhkAdj).2 (by rwa [hshared])
  have hhFace : fwr_faceInside c h := by
    simpa [fwr_faceInside, phb_doubleDualEquiv,
      phb_doubleDualShift, jec_mem_leftRegion] using hhInside
  have hkFace : ¬ fwr_faceInside c k := hsplit.mp hhFace
  simpa [fwr_faceInside, phb_doubleDualEquiv,
    phb_doubleDualShift, jec_mem_leftRegion] using hkFace


theorem rlc_centralRegion_inside_firstIntersectionCycle
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    ∃ (c : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)),
      c.IsCycle ∧
        (∀ e ∈ c.edges,
          e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧
        (∀ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
          phb_doubleDualEquiv.symm h ∈ jec_leftRegion c) ∧
        ∀ {x y : Site 2},
          s(x, y) ∈ ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).edges →
          s(x, y) ∈ c.edges ∨
            ∀ h ∈ flankFaces x y,
              phb_doubleDualEquiv.symm h ∉ jec_leftRegion c := by
  obtain ⟨c, hcycle, _hlower, _hupper, hedges, hodd,
    hleftDichotomy⟩ :=
    rlc_bookFirstIntersectionFourTraceAxisCycle_of_faithful
      gamma gamma' hfaith
  refine ⟨c, hcycle, hedges, ?_, hleftDichotomy⟩
  intro h hhRegion
  have hn : 0 < n := by
    have hrect := rlc_pathVertex_mem_rect gamma.1
      (rlc_path_start_mem_vertices gamma.1)
    rw [mem_rect] at hrect
    have := hfaith.right_axis_strict
    omega
  have hcentralRegion : rlc_connectorCentralFace ∈
      rlc_connectorCentralFaceRegion gamma gamma' :=
    rlc_connectorCentralFace_mem_region gamma gamma' hn
  obtain ⟨hsBox, hhBox, hreach⟩ :=
    rlc_connectorCentralFaceRegion_reachable hcentralRegion hhRegion
  obtain ⟨w⟩ := hreach
  have hstep {x y : RlcConnectorFaceVertex n}
      (hxy : (rlc_connectorFiniteFaceCutGraph gamma gamma').Adj x y) :
      fwr_faceInside c x.1 ↔ fwr_faceInside c y.1 := by
    have hcut := (rlc_connectorFourTraceFaceCutGraph_adj
      gamma gamma' x.1 y.1).mp hxy
    have hnot : sharedPrimalEdge x.1 y.1 ∉ c.edges := by
      intro hc
      exact hcut.2 (hedges _ hc)
    have hmatch := fwr_faceCutMatch_of_nodup
      c hcycle.edges_nodup hcut.1
    have hnosplit : ¬ (fwr_faceInside c x.1 ↔
        ¬ fwr_faceInside c y.1) := by
      intro hsplit
      exact hnot (hmatch.mp hsplit)
    tauto
  have hpropagate {x y : RlcConnectorFaceVertex n}
      (p : (rlc_connectorFiniteFaceCutGraph gamma gamma').Walk x y) :
      fwr_faceInside c x.1 → fwr_faceInside c y.1 := by
    intro hx
    induction p with
    | nil => exact hx
    | @cons u v z huv p ih =>
        exact ih ((hstep huv).mp hx)
  have hcentralInside : fwr_faceInside c rlc_connectorCentralFace := by
    have hgap := hodd 1 (by
        have := hfaith.right_axis_strict
        omega) (by
        have := hfaith.left_axis_strict
        omega)
    simpa [fwr_faceInside, rlc_connectorCentralFace] using hgap
  have hhInside := hpropagate w hcentralInside
  simpa [fwr_faceInside, phb_doubleDualEquiv,
    phb_doubleDualShift, jec_mem_leftRegion] using hhInside


theorem rlc_walk_all_edges_or_last_failure_decomp
    {V : Type*} {G : SimpleGraph V} (P : Sym2 V → Prop)
    {x y : V} (w : G.Walk x y) :
    (∀ e ∈ w.edges, P e) ∨
      ∃ (u v : V) (p : G.Walk x u) (r : G.Walk v y)
        (huv : G.Adj u v),
        ¬ P s(u, v) ∧
          (∀ e ∈ r.edges, P e) ∧
          w = p.append (.cons huv r) := by
  induction w with
  | nil =>
      left
      simp
  | @cons a b c hab t ih =>
      rcases ih with hall | ⟨u, v, p, r, huv, hfail, hsuffix, hdecomp⟩
      · by_cases habP : P s(a, b)
        · left
          intro e he
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
          exact he.elim (fun h => h ▸ habP) (fun h => hall e h)
        · right
          exact ⟨a, b, .nil, t, hab, habP, hall, by simp⟩
      · right
        refine ⟨u, v, .cons hab p, r, huv, hfail, hsuffix, ?_⟩
        rw [hdecomp]
        rfl


end
end StatMech.Universality
