/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part43
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_goodComponent_or_firstIntersectionOrderedBad
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∨
      RlcTwoChannelFullPhysicalFirstIntersectionOrderedBadSeparation
        gamma gamma' omega := by
  obtain ⟨z, x, y, right, flipLeft, hzRight, hzLeft,
      hxSupport, hySupport, hxPath, hyPath, hxOrder, hyOrder,
      _hflipLeftRank, _hfirst, _hrankRealized, _hglobalMin⟩ :=
    rlc_twoChannelFullPhysical_firstIntersectionOrderedContacts_of_failure
      gamma gamma' hfaith omega hno
  by_cases hxy : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Reachable x y
  · exact Or.inl ⟨x, y, hxy, hxPath, hyPath⟩
  ·
    obtain ⟨w⟩ := rlc_twoChannelFullFilledFaceBoundary_reachable
      gamma gamma' omega hxSupport hySupport
    rcases rlc_walk_subgraph_lift_or_first_exit_decomp
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
          gamma gamma' omega) w with
      ⟨q, hq⟩ | ⟨u, v, q, r, huv, huvBad, hdecomp⟩
    · exact False.elim (hxy q.reachable)
    · have hbad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' u v := by
        intro hcarrier
        exact huvBad
          ((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
            gamma gamma' omega).2 ⟨huv, hcarrier⟩)
      have hxBarrier : rlc_dualReflect x ∈
          rlc_connectorBarrier gamma gamma' := by
        simp [rlc_connectorBarrier, hxPath]
      have hxBox : rlc_dualReflect x ∈ rlc_connectorBox n := by
        simpa [rlc_connectorBox] using
          (rlc_rightPathVertex_mem_connectorBox gamma hxPath)
      have hclass :
          RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∨
          (((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
                gamma gamma' u v) ∧
              (rlc_dualReflect u ∈ rlc_pathVertices gamma.1 ∨
                (0 < (rlc_dualReflect u) 0 ∧
                  ∃ w ∈ rlc_pathVertices gamma'.1,
                    rlc_dualReflect u = rlc_flipX w) ∨
                ((rlc_dualReflect u) 0 < 0 ∧
                  ∃ w ∈ rlc_pathVertices gamma.1,
                    rlc_dualReflect u = rlc_flipX w) ∨
                (rlc_dualReflect u) 0 = -2 * n ∨
                (rlc_dualReflect u) 0 = 2 * n ∨
                (rlc_dualReflect u) 1 = -n ∨
                (rlc_dualReflect u) 1 = n)) ∨
            ∃ p q : Site 2,
              sharedPrimalEdge u v = s(p, q) ∧
                (hypercubicLattice 2).Adj p q ∧
                p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
                q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
                (p ∈ rlc_pathVertices gamma.1 ∨
                  (0 < p 0 ∧ ∃ w ∈ rlc_pathVertices gamma'.1,
                    p = rlc_flipX w) ∨
                  (p 0 < 0 ∧ ∃ w ∈ rlc_pathVertices gamma.1,
                    p = rlc_flipX w) ∨
                  p 0 = -2 * n ∨ p 0 = 2 * n ∨
                  p 1 = -n ∨ p 1 = n)) := by
        rcases rlc_twoChannelFullPhysical_boundaryBad_target_or_sourceNotPlanar
            gamma gamma' omega huv hbad with htarget | hsource
        · have hplace :=
            rlc_twoChannelFullPhysical_targetBad_near_barrier_or_boxBoundary
              hxBarrier hxBox q huv htarget
          rcases hplace with huBarrier | huBoundary
          · rcases rlc_connectorBarrier_original_or_strict_reflected
                gamma gamma' huBarrier with
              huRight | huLeft | huFlipLeft | huFlipRight
            · exact Or.inr (Or.inl ⟨htarget, Or.inl huRight⟩)
            · exact Or.inl ⟨x, u, q.reachable, hxPath, huLeft⟩
            · exact Or.inr (Or.inl ⟨htarget,
                Or.inr (Or.inl huFlipLeft)⟩)
            · exact Or.inr (Or.inl ⟨htarget,
                Or.inr (Or.inr (Or.inl huFlipRight))⟩)
          · exact Or.inr (Or.inl ⟨htarget,
              Or.inr (Or.inr (Or.inr huBoundary))⟩)
        · obtain ⟨p, s, hps, hpsAdj, hpReach, hsFilled, hpPlace⟩ :=
            rlc_twoChannelFullPhysical_sourceBad_inside_barrier_or_boxBoundary
              gamma gamma' omega huv hsource
          have hsourceResult :
              ∃ p q : Site 2,
                sharedPrimalEdge u v = s(p, q) ∧
                  (hypercubicLattice 2).Adj p q ∧
                  p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
                  q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
                  (p ∈ rlc_pathVertices gamma.1 ∨
                    (0 < p 0 ∧ ∃ w ∈ rlc_pathVertices gamma'.1,
                      p = rlc_flipX w) ∨
                    (p 0 < 0 ∧ ∃ w ∈ rlc_pathVertices gamma.1,
                      p = rlc_flipX w) ∨
                    p 0 = -2 * n ∨ p 0 = 2 * n ∨
                    p 1 = -n ∨ p 1 = n) := by
            refine ⟨p, s, hps, hpsAdj, hpReach, hsFilled, ?_⟩
            rcases hpPlace with hpBarrier | hpBoundary
            · rcases rlc_connectorBarrier_original_or_strict_reflected
                  gamma gamma' hpBarrier with
                hpRight | hpLeft | hpFlipLeft | hpFlipRight
              · exact Or.inl hpRight
              · exact False.elim
                  ((rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
                    gamma gamma' omega hno hpLeft) hpReach)
              · exact Or.inr (Or.inl hpFlipLeft)
              · exact Or.inr (Or.inr (Or.inl hpFlipRight))
            · exact Or.inr (Or.inr (Or.inr hpBoundary))
          exact Or.inr (Or.inr hsourceResult)
      rcases hclass with hgood | hclass
      · exact Or.inl hgood
      · refine Or.inr ⟨z, x, y, u, v, right, flipLeft,
        hzRight, hzLeft, hxPath, hyPath, hxOrder, hyOrder,
        q.reachable, huv, ?_, hclass⟩
        exact r.reachable


theorem rlc_isCycles_isPath_eq_of_snd_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hcycles : G.IsCycles) {x y : V}
    (p q : G.Walk x y) (hpPath : p.IsPath) (hqPath : q.IsPath)
    (hxy : x ≠ y) (hsnd : p.snd = q.snd) : p = q := by
  induction p with
  | nil => exact False.elim (hxy rfl)
  | @cons x v y h p ih =>
      cases q with
      | nil => exact False.elim (hxy rfl)
      | @cons _ w _ e q =>
          have hvw : v = w := by
            simpa [SimpleGraph.Walk.snd] using hsnd
          subst w
          have hpTail : p.IsPath := hpPath.of_cons
          have hqTail : q.IsPath := hqPath.of_cons
          by_cases hvy : v = y
          · subst v
            have hpNil : p = .nil :=
              (SimpleGraph.Walk.isPath_iff_eq_nil p).mp hpTail
            have hqNil : q = .nil :=
              (SimpleGraph.Walk.isPath_iff_eq_nil q).mp hqTail
            subst p
            subst q
            rfl
          · have hxNotP : x ∉ p.support :=
              (SimpleGraph.Walk.cons_isPath_iff h p).mp hpPath |>.2
            have hxNotQ : x ∉ q.support :=
              (SimpleGraph.Walk.cons_isPath_iff e q).mp hqPath |>.2
            have hpNotNil : ¬p.Nil := p.not_nil_of_ne hvy
            have hqNotNil : ¬q.Nil := q.not_nil_of_ne hvy
            have hpNext : x ≠ p.snd ∧ G.Adj v p.snd := by
              refine ⟨?_, p.adj_snd hpNotNil⟩
              intro heq
              apply hxNotP
              rw [heq]
              exact p.getVert_mem_support 1
            have hqNext : x ≠ q.snd ∧ G.Adj v q.snd := by
              refine ⟨?_, q.adj_snd hqNotNil⟩
              intro heq
              apply hxNotQ
              rw [heq]
              exact q.getVert_mem_support 1
            obtain ⟨other, _hother, hunique⟩ :=
              hcycles.existsUnique_ne_adj h.symm
            have hpOther : p.snd = other := hunique p.snd hpNext
            have hqOther : q.snd = other := hunique q.snd hqNext
            have hpq : p = q := ih q hpTail hqTail hvy
              (hpOther.trans hqOther.symm)
            subst q
            rfl


theorem rlc_isCycles_isPath_eq_ordered_or_complementary
    {H : SimpleGraph (Site 2)} (hcycles : H.IsCycles)
    {u x y : Site 2} (c : H.Walk u u) (hc : c.IsCycle)
    (hx : x ∈ c.support) (hy : y ∈ c.support) (hxy : x ≠ y)
    (p : H.Walk x y) (hp : p.IsPath) :
    p = rlc_orderedContourArc c hx hy ∨
      p = rlc_complementaryContourArc c hx hy := by
  let a := rlc_orderedContourArc c hx hy
  let b := rlc_complementaryContourArc c hx hy
  have haPath : a.IsPath :=
    rlc_orderedContourArc_isPath c hc hx hy
  have hbPath : b.IsPath :=
    rlc_complementaryContourArc_isPath c hc hx hy hxy
  have hpNonNil : ¬p.Nil := p.not_nil_of_ne hxy
  have haNonNil : ¬a.Nil := a.not_nil_of_ne hxy
  have hbNonNil : ¬b.Nil := b.not_nil_of_ne hxy
  have habSnd : a.snd ≠ b.snd := by
    intro hsnd
    have haEdge : s(x, a.snd) ∈ a.edges :=
      a.mk_start_snd_mem_edges haNonNil
    have hbEdge : s(x, b.snd) ∈ b.edges :=
      b.mk_start_snd_mem_edges hbNonNil
    exact (rlc_orderedContourArc_edges_disjoint_complementary
      c hc.isTrail hx hy) haEdge (hsnd ▸ hbEdge)
  by_cases hpa : p.snd = a.snd
  · exact Or.inl (rlc_isCycles_isPath_eq_of_snd_eq
      hcycles p a hp haPath hxy hpa)
  · right
    have haAdj : H.Adj x a.snd := a.adj_snd haNonNil
    obtain ⟨other, _hother, hunique⟩ :=
      hcycles.existsUnique_ne_adj haAdj
    have hpOther : p.snd = other :=
      hunique p.snd ⟨fun h => hpa h.symm, p.adj_snd hpNonNil⟩
    have hbOther : b.snd = other :=
      hunique b.snd ⟨habSnd, b.adj_snd hbNonNil⟩
    exact rlc_isCycles_isPath_eq_of_snd_eq
      hcycles p b hp hbPath hxy (hpOther.trans hbOther.symm)


theorem rlc_twoChannelFullPhysical_contactCycle_of_boundaryContacts
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x y : Site 2}
    (hxSupport : x ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (hySupport : y ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
    ∃ (u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u),
      c.IsCycle ∧ x ∈ c.support ∧ y ∈ c.support := by
  let G := faceBoundaryGraph
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  have hxy : G.Reachable x y :=
    rlc_twoChannelFullFilledFaceBoundary_reachable
      gamma gamma' omega hxSupport hySupport
  obtain ⟨z, hxz⟩ := hxSupport
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (rlc_twoChannelFullFilledReachSet_finite gamma gamma' omega)
  obtain ⟨u, c, hcycle, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      G T hT
      (degree_faceBoundaryGraph_even
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)) hxz
  have hxCycle : x ∈ c.support := c.fst_mem_support_of_mem_edges hedge
  have hcycles :=
    rlc_twoChannelFullFilledBoundary_isCycles gamma gamma' omega
  have hstep {a b : Site 2} (ha : a ∈ c.support) (hab : G.Adj a b) :
      b ∈ c.support := by
    have haVerts : a ∈ c.toSubgraph.verts := by
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using ha
    have habSub : c.toSubgraph.Adj a b :=
      (hcycle.adj_toSubgraph_iff_of_isCycles hcycles haVerts b).2 hab
    simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using
      c.toSubgraph.edge_vert habSub.symm
  have hwalk {a b : Site 2} (w : G.Walk a b) (ha : a ∈ c.support) :
      b ∈ c.support := by
    induction w with
    | nil => exact ha
    | @cons a b d hab w ih => exact ih (hstep ha hab)
  obtain ⟨w⟩ := hxy
  exact ⟨u, c, hcycle, hxCycle, hwalk w hxCycle⟩


theorem rlc_twoChannelFullPhysical_contactCycle_covers
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x u : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hxSupport : x ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (hxCycle : x ∈ c.support) :
    ∀ e ∈ (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).edgeSet,
      e ∈ c.edges := by
  let G := faceBoundaryGraph
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  have hcycles :=
    rlc_twoChannelFullFilledBoundary_isCycles gamma gamma' omega
  have hstep {a b : Site 2} (ha : a ∈ c.support) (hab : G.Adj a b) :
      b ∈ c.support := by
    have haVerts : a ∈ c.toSubgraph.verts := by
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using ha
    have habSub : c.toSubgraph.Adj a b :=
      (hcycle.adj_toSubgraph_iff_of_isCycles hcycles haVerts b).2 hab
    simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using
      c.toSubgraph.edge_vert habSub.symm
  have hwalk {a b : Site 2} (w : G.Walk a b) (ha : a ∈ c.support) :
      b ∈ c.support := by
    induction w with
    | nil => exact ha
    | @cons a b d hab w ih => exact ih (hstep ha hab)
  intro e he
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : G.Adj a b := he
      have haSupport : a ∈ G.support := hab.mem_support_left
      have hxa : G.Reachable x a :=
        rlc_twoChannelFullFilledFaceBoundary_reachable
          gamma gamma' omega hxSupport haSupport
      obtain ⟨w⟩ := hxa
      have haCycle : a ∈ c.support := hwalk w hxCycle
      have haVerts : a ∈ c.toSubgraph.verts := by
        simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using haCycle
      have habSub : c.toSubgraph.Adj a b :=
        (hcycle.adj_toSubgraph_iff_of_isCycles hcycles haVerts b).2 hab
      exact c.adj_toSubgraph_iff_mem_edges.mp habSub


theorem rlc_twoChannelFullPhysical_contactCycle_support_of_boundarySupport
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u a v : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (haSupport : a ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (haCycle : a ∈ c.support)
    (hvSupport : v ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
    v ∈ c.support := by
  obtain ⟨w, hvw⟩ := hvSupport
  have hvwCycle : s(v, w) ∈ c.edges :=
    rlc_twoChannelFullPhysical_contactCycle_covers
      gamma gamma' omega c hcycle haSupport haCycle s(v, w) hvw
  exact c.fst_mem_support_of_mem_edges hvwCycle


theorem rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x u : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hxSupport : x ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (hxCycle : x ∈ c.support) :
    rlc_twoChannelFullFilledReachSet gamma gamma' omega =
      jec_leftRegion (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
  apply rlc_leftRegion_eq_of_faceBoundaryTrail
  · exact rlc_twoChannelFullFilledReachSet_finite gamma gamma' omega
  · exact hcycle.isTrail
  · exact rlc_twoChannelFullPhysical_contactCycle_covers
      gamma gamma' omega c hcycle hxSupport hxCycle


theorem rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) :
    rlc_twoChannelFullFilledReachSet gamma gamma' omega =
      jec_leftRegion (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
  have hcNotNil : ¬c.Nil := by
    intro hnil
    exact hcycle.ne_nil hnil.eq_nil
  have huSupport : u ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support :=
    (c.adj_snd hcNotNil).mem_support_left
  exact rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion
    gamma gamma' omega c hcycle huSupport c.start_mem_support


theorem rlc_twoChannelFullPhysical_boundary_leftRegionTransition
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x u f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hxSupport : x ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (hxCycle : x ∈ c.support)
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g) :
    ∃ p q : Site 2,
      sharedPrimalEdge f g = s(p, q) ∧
        (hypercubicLattice 2).Adj p q ∧
        p ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧
        q ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧
        (p ∈ (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).support ∨
          q ∈ (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).support) := by
  obtain ⟨p, q, hpq, hpqAdj, hpReach, hqOut⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideSourceWitness
      gamma gamma' omega hfg
  have hregion := rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion
    gamma gamma' omega c hcycle hxSupport hxCycle
  have hpFilled :=
    rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega hpReach
  have hpInside : p ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rwa [← hregion]
  have hqOutside : q ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rwa [← hregion]
  refine ⟨p, q, hpq, hpqAdj, hpInside, hqOutside, ?_⟩
  apply jec_leftRegion_bdEdge_support
    (c.mapLe (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) hpqAdj
  rw [bdEdge_mk]
  exact ⟨fun _ => hqOutside, fun _ => hpInside⟩


theorem rlc_twoChannelFullPhysical_boundary_insideSourceWalk_leftRegion
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x u f g f' g' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hxSupport : x ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
    (hxCycle : x ∈ c.support)
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
    (hfg' : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f' g') :
    ∃ (p q p' q' : Site 2)
      (w : (hypercubicLattice 2).Walk p p'),
      sharedPrimalEdge f g = s(p, q) ∧
        sharedPrimalEdge f' g' = s(p', q') ∧
        (hypercubicLattice 2).Adj p q ∧
        (hypercubicLattice 2).Adj p' q' ∧
        q ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧
        q' ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧
        (∀ z ∈ w.support,
          z ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) ∧
        (p ∈ (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).support ∨
          q ∈ (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).support) ∧
        (p' ∈ (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).support ∨
          q' ∈ (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).support) := by
  obtain ⟨p, q, p', q', w, hpq, hpq', hpqAdj, hpqAdj',
      _hpReach, _hpReach', hqOut, hqOut', hwReach⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideSourceWalk
      gamma gamma' omega hfg hfg'
  have hregion := rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion
    gamma gamma' omega c hcycle hxSupport hxCycle
  have hqOutside : q ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rwa [← hregion]
  have hqOutside' : q' ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rwa [← hregion]
  have hwInside : ∀ z ∈ w.support,
      z ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    intro z hz
    rw [← hregion]
    exact rlc_twoChannelFullReachSet_subset_filled
      gamma gamma' omega (hwReach z hz).1
  have hpInside := hwInside p w.start_mem_support
  have hpInside' := hwInside p' w.end_mem_support
  refine ⟨p, q, p', q', w, hpq, hpq', hpqAdj, hpqAdj',
    hqOutside, hqOutside', hwInside, ?_, ?_⟩
  · apply jec_leftRegion_bdEdge_support
      (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) hpqAdj
    rw [bdEdge_mk]
    exact ⟨fun _ => hqOutside, fun _ => hpInside⟩
  · apply jec_leftRegion_bdEdge_support
      (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) hpqAdj'
    rw [bdEdge_mk]
    exact ⟨fun _ => hqOutside', fun _ => hpInside'⟩


theorem rlc_twoChannelFullPhysical_firstIntersectionContactCycle_of_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ∃ (z x y u : Site 2)
      (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
      (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u),
      c.IsCycle ∧ x ∈ c.support ∧ y ∈ c.support ∧
        z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        rlc_flipX (rlc_dualReflect x) ∈
          (right.map rlc_flipXLatticeHom).support ∧
        rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧
        RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧
        (∀ w ∈ right.support,
          rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z) ∧
        RlcBookRightIntersectionRankRealizedAt gamma right ∧
        RlcBookRightIntersectionRankMinimalAt gamma gamma' right := by
  obtain ⟨z, x, y, right, flipLeft, hzRight, hzLeft,
      hxSupport, hySupport, hxPath, hyPath, hxOrder, hyOrder,
      hflipLeftRank, hfirst, hrankRealized, hglobalMin⟩ :=
    rlc_twoChannelFullPhysical_firstIntersectionOrderedContacts_of_failure
      gamma gamma' hfaith omega hno
  obtain ⟨u, c, hcycle, hx, hy⟩ :=
    rlc_twoChannelFullPhysical_contactCycle_of_boundaryContacts
      gamma gamma' omega hxSupport hySupport
  exact ⟨z, x, y, u, right, flipLeft, c, hcycle, hx, hy,
    hzRight, hzLeft, hxPath, hyPath, hxOrder, hyOrder, hflipLeftRank,
    hfirst, hrankRealized, hglobalMin⟩


theorem rlc_twoChannelFullPhysical_contactCycle_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ∃ (x y u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u),
      c.IsCycle ∧ x ∈ c.support ∧ y ∈ c.support ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 := by
  let G := faceBoundaryGraph
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ :=
    rlc_twoChannelFullFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith omega hno
  have hxy : G.Reachable x y :=
    rlc_twoChannelFullFilledFaceBoundary_reachable
      gamma gamma' omega hxSupport hySupport
  obtain ⟨z, hxz⟩ := hxSupport
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph
    (rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (rlc_twoChannelFullFilledReachSet_finite gamma gamma' omega)
  obtain ⟨u, c, hcycle, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      G T hT
      (degree_faceBoundaryGraph_even
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)) hxz
  have hxCycle : x ∈ c.support := c.fst_mem_support_of_mem_edges hedge
  have hcycles :=
    rlc_twoChannelFullFilledBoundary_isCycles gamma gamma' omega
  have hstep {a b : Site 2} (ha : a ∈ c.support) (hab : G.Adj a b) :
      b ∈ c.support := by
    have haVerts : a ∈ c.toSubgraph.verts := by
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using ha
    have habSub : c.toSubgraph.Adj a b :=
      (hcycle.adj_toSubgraph_iff_of_isCycles hcycles haVerts b).2 hab
    simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using
      c.toSubgraph.edge_vert habSub.symm
  have hwalk {a b : Site 2} (w : G.Walk a b) (ha : a ∈ c.support) :
      b ∈ c.support := by
    induction w with
    | nil => exact ha
    | @cons a b d hab w ih => exact ih (hstep ha hab)
  obtain ⟨w⟩ := hxy
  have hyCycle : y ∈ c.support := by
    exact hwalk w hxCycle
  exact ⟨x, y, u, c, hcycle, hxCycle, hyCycle, hxPath, hyPath⟩


theorem rlc_twoChannelFullPhysical_contactCycle_of_staticCut
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
    ∃ (x y u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig
            gamma gamma' A))).Walk u u),
      c.IsCycle ∧ x ∈ c.support ∧ y ∈ c.support ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 := by
  exact rlc_twoChannelFullPhysical_contactCycle_of_faithful_failure
    gamma gamma' hfaith
    (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
    (rlc_twoChannelFullPhysicalCutInteriorConfig_failure
      gamma gamma' A hAright hAleft)


end
end StatMech.Universality
