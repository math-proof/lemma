/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_twoChannelFullReachSet_subset_box {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullReachSet gamma gamma' omega ⊆
      rect (-2 * n) (2 * n) (-n) n := by
  rintro z ⟨hz, _⟩
  exact hz

theorem rlc_twoChannelFullReachSet_finite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    (rlc_twoChannelFullReachSet gamma gamma' omega).Finite :=
  (rect_finite (-2 * n) (2 * n) (-n) n).subset
    (rlc_twoChannelFullReachSet_subset_box gamma gamma' omega)


theorem rlc_rightPathVertex_mem_twoChannelFullReachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {z : Site 2}
    (hz : z ∈ rlc_pathVertices gamma.1) :
    z ∈ rlc_twoChannelFullReachSet gamma gamma' omega := by
  let z' : RlcConnectorVertex n :=
    ⟨z, rlc_rightPathVertex_mem_connectorBox gamma hz⟩
  have htrace := rlc_connectorTraceWiring_reachable_right gamma gamma'
    (rlc_connectorRightAnchor_onRight gamma)
      (show rlc_connectorOnRight gamma z' from hz)
  have hsource :
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).Reachable
          (rlc_connectorRightAnchor gamma) z' := by
    rw [rlc_openSub_twoChannelAugmented_forceTrace]
    exact htrace.mono le_sup_right
  refine ⟨z'.2, ?_⟩
  change (openSubgraphInduce 2
    (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
    (rect (-2 * n) (2 * n) (-n) n)).Reachable
      ⟨(rlc_connectorRightAnchor gamma : Site 2),
        (rlc_connectorRightAnchor gamma).2⟩ ⟨z, z'.2⟩
  rw [← rlc_openSub_twoChannelAugmented_forceTrace_eq_fullAmbientInduce]
  exact hsource


theorem rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {z : Site 2} (hz : z ∈ rlc_pathVertices gamma'.1) :
    z ∉ rlc_twoChannelFullReachSet gamma gamma' omega := by
  rintro ⟨hzBox, hzReach⟩
  let z' : RlcConnectorVertex n := ⟨z, hzBox⟩
  have hzSource :
      (FK.openSub
        (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G
        (rlc_connectorForceTraceConfig gamma gamma'
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).Reachable
          (rlc_connectorRightAnchor gamma) z' := by
    rw [rlc_openSub_twoChannelAugmented_forceTrace_eq_fullAmbientInduce]
    exact hzReach
  have hleft := rlc_connectorTraceWiring_reachable_left gamma gamma'
    (show rlc_connectorOnLeft gamma' z' from hz)
      (rlc_connectorLeftAnchor_onLeft gamma')
  rw [rlc_openSub_twoChannelAugmented_forceTrace] at hzSource
  have hanchors := hzSource.trans (hleft.mono
    (show rlc_connectorTraceWiring gamma gamma' ≤
      FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) ⊔
        rlc_connectorTraceWiring gamma gamma' from le_sup_right))
  exact hno ((rlc_exists_connector_iff_traceAnchors gamma gamma'
    (FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_twoChannelEdgeConfigExtend gamma gamma' omega))).mpr hanchors)


theorem rlc_twoChannelFullReachSet_extend {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {v w : Site 2}
    (hv : v ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hw : w ∈ rect (-2 * n) (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hopen : rlc_twoChannelFullAmbientConfig gamma gamma' omega
      s(v, w) = true) :
    w ∈ rlc_twoChannelFullReachSet gamma gamma' omega := by
  obtain ⟨hvBox, hvReach⟩ := hv
  refine ⟨hw, hvReach.trans ?_⟩
  exact (show (openSubgraphInduce 2
    (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
    (rect (-2 * n) (2 * n) (-n) n)).Adj
      ⟨v, hvBox⟩ ⟨w, hw⟩ from ⟨hadj, hopen⟩).reachable


theorem rlc_twoChannelFullReachSet_edgeBoundary_closed {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {v w : Site 2}
    (hvw : (v, w) ∈ edgeBoundary 2
      (rlc_twoChannelFullReachSet gamma gamma' omega)) :
    rlc_twoChannelFullAmbientConfig gamma gamma' omega s(v, w) = false := by
  obtain ⟨hadj, hsplit⟩ := hvw
  by_cases hv : v ∈ rlc_twoChannelFullReachSet gamma gamma' omega
  · have hw : w ∉ rlc_twoChannelFullReachSet gamma gamma' omega := hsplit.mp hv
    by_contra hopen
    rw [Bool.not_eq_false] at hopen
    have hedge := rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
      gamma gamma' omega hopen
    have hwBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
      gamma gamma' hedge (Sym2.mem_mk_right v w)
    exact hw (rlc_twoChannelFullReachSet_extend gamma gamma' omega hv
      (by simpa [rlc_connectorBox] using hwBox) hadj hopen)
  · have hw : w ∈ rlc_twoChannelFullReachSet gamma gamma' omega := by
      by_contra hw
      exact hv (hsplit.mpr hw)
    rw [Sym2.eq_swap]
    by_contra hopen
    rw [Bool.not_eq_false] at hopen
    have hedge := rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
      gamma gamma' omega hopen
    have hvBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
      gamma gamma' hedge (Sym2.mem_mk_right w v)
    exact hv (rlc_twoChannelFullReachSet_extend gamma gamma' omega hw
      (by simpa [rlc_connectorBox] using hvBox) hadj.symm hopen)


theorem rlc_twoChannelFullBoundary_le_openFaceDual {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    faceBoundaryGraph (rlc_twoChannelFullReachSet gamma gamma' omega) ≤
      openSubgraph 2 (fci_faceDualConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega)) := by
  intro f g hfg
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_twoChannelFullReachSet gamma gamma' omega) := by
    refine ⟨hpqAdj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hclosed := rlc_twoChannelFullReachSet_edgeBoundary_closed
    gamma gamma' omega hpqBoundary
  refine ⟨hfg.1, ?_⟩
  rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1, hpq]
  simpa using hclosed


theorem rlc_twoChannelFullReachSet_edgeBoundary_nonempty {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    (edgeBoundary 2
      (rlc_twoChannelFullReachSet gamma gamma' omega)).Nonempty := by
  let v : Site 2 := gamma.1.2.1
  let w : Site 2 := v + ![1, 0]
  have hvPath : v ∈ rlc_pathVertices gamma.1 :=
    rlc_connector_path_end_mem_vertices gamma.1
  have hv : v ∈ rlc_twoChannelFullReachSet gamma gamma' omega :=
    rlc_rightPathVertex_mem_twoChannelFullReachSet gamma gamma' omega hvPath
  have hvx : v 0 = 2 * n := by
    simpa only [v] using gamma.1.2.1.2.2
  have hw0 : w 0 = v 0 + 1 := by
    change ((v + (![1, 0] : Site 2) : Site 2) 0) = v 0 + 1
    rw [Pi.add_apply]
    rfl
  have hw1 : w 1 = v 1 := by
    change ((v + (![1, 0] : Site 2) : Site 2) 1) = v 1
    rw [Pi.add_apply]
    simp
  have hadj : (hypercubicLattice 2).Adj v w := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two, hw0, hw1]
    simp
  have hw : w ∉ rlc_twoChannelFullReachSet gamma gamma' omega := by
    intro hwReach
    have hwR := rlc_twoChannelFullReachSet_subset_box
      gamma gamma' omega hwReach
    rw [mem_rect] at hwR
    have : w 0 = 2 * n + 1 := by rw [hw0, hvx]
    omega
  exact ⟨(v, w), hadj, iff_of_true hv hw⟩


theorem rlc_twoChannelFullReachSet_dualCircuit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ∃ (u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullReachSet gamma gamma' omega)).Walk u u),
      c.IsCycle := by
  obtain ⟨⟨v, w⟩, hvw⟩ :=
    rlc_twoChannelFullReachSet_edgeBoundary_nonempty gamma gamma' omega
  exact exists_dualCircuit_of_finite_of_edgeBoundary
    (rlc_twoChannelFullReachSet gamma gamma' omega)
    (rlc_twoChannelFullReachSet_finite gamma gamma' omega) hvw


theorem rlc_twoChannelFullReachSet_openFaceDualCircuit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ∃ (u : Site 2)
      (c : (openSubgraph 2 (fci_faceDualConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Walk u u),
      c.IsCycle := by
  obtain ⟨u, c, hcyc⟩ :=
    rlc_twoChannelFullReachSet_dualCircuit gamma gamma' omega
  let hle := rlc_twoChannelFullBoundary_le_openFaceDual gamma gamma' omega
  exact ⟨u, c.mapLe hle, hcyc.mapLe hle⟩


theorem rlc_twoChannelFullReachSet_reflectedOpenDualCircuit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    ∃ (u : Site 2)
      (c : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Walk
          (rlc_dualReflect u) (rlc_dualReflect u)),
      c.IsCycle := by
  obtain ⟨u, c, hcyc⟩ :=
    rlc_twoChannelFullReachSet_openFaceDualCircuit gamma gamma' omega
  exact ⟨u, rlc_dualReflectOpenWalk _ c,
    rlc_dualReflectOpenWalk_isCycle _ hcyc⟩


theorem rlc_twoChannelFullReachSet_axis_boundary_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ∃ p q : Site 2,
      (p, q) ∈ edgeBoundary 2
        (rlc_twoChannelFullReachSet gamma gamma' omega) ∧
      p ∈ rect (-2 * n) (2 * n) (-n) n ∧
      q ∈ rect (-2 * n) (2 * n) (-n) n ∧
      p 0 = 0 ∧ q 0 = 0 := by
  let x : Site 2 := gamma.1.1
  let y : Site 2 := gamma'.1.2.1
  have hxPath : x ∈ rlc_pathVertices gamma.1 :=
    rlc_path_start_mem_vertices gamma.1
  have hyPath : y ∈ rlc_pathVertices gamma'.1 :=
    rlc_connector_path_end_mem_vertices gamma'.1
  have hxReach := rlc_rightPathVertex_mem_twoChannelFullReachSet
    gamma gamma' omega hxPath
  have hyNot :=
    rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
      gamma gamma' omega hno hyPath
  have hx0 : x 0 = 0 := gamma.1.1.2.2
  have hy0 : y 0 = 0 := gamma'.1.2.1.2.2
  have hxx : x = ![0, x 1] := by
    ext i
    fin_cases i <;> simp [hx0]
  have hyy : y = ![0, y 1] := by
    ext i
    fin_cases i <;> simp [hy0]
  let w : (hypercubicLattice 2).Walk x y :=
    (sw_vertSeg 0 (x 1) (y 1)).copy hxx.symm hyy.symm
  obtain ⟨p, q, hpq, hpqEdge⟩ := rlc_walk_mem_edgeBoundary_edges
    (rlc_twoChannelFullReachSet gamma gamma' omega) w hxReach hyNot
  have hpSupp : p ∈ w.support := w.fst_mem_support_of_mem_edges hpqEdge
  have hqSupp : q ∈ w.support := w.snd_mem_support_of_mem_edges hpqEdge
  have hsupport (z : Site 2) (hz : z ∈ w.support) :
      ∃ t : Int, t ∈ Set.uIcc (x 1) (y 1) ∧ z = ![0, t] := by
    change z ∈ ((sw_vertSeg 0 (x 1) (y 1)).copy _ _).support at hz
    rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hz
    exact hz
  obtain ⟨tp, htp, rfl⟩ := hsupport p hpSupp
  obtain ⟨tq, htq, rfl⟩ := hsupport q hqSupp
  have hxRows : -n ≤ x 1 ∧ x 1 ≤ n := by
    have h := gamma.1.1.2.1
    rw [mem_rect] at h
    exact h.2.2
  have hyRows : -n ≤ y 1 ∧ y 1 ≤ n := by
    have h := gamma'.1.2.1.2.1
    rw [mem_rect] at h
    exact h.2.2
  have htpRows : -n ≤ tp ∧ tp ≤ n := by
    rw [Set.mem_uIcc] at htp
    rcases htp with htp | htp <;> omega
  have htqRows : -n ≤ tq ∧ tq ≤ n := by
    rw [Set.mem_uIcc] at htq
    rcases htq with htq | htq <;> omega
  refine ⟨![0, tp], ![0, tq], hpq, ?_, ?_, by simp, by simp⟩
  · rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  · rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega


theorem rlc_twoChannelFullReachSet_axis_anchored_dualCircuit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma') :
    ∃ (p q f g u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_twoChannelFullReachSet gamma gamma' omega)).Walk u u),
      (p, q) ∈ edgeBoundary 2
        (rlc_twoChannelFullReachSet gamma gamma' omega) ∧
      p ∈ rect (-2 * n) (2 * n) (-n) n ∧
      q ∈ rect (-2 * n) (2 * n) (-n) n ∧
      p 0 = 0 ∧ q 0 = 0 ∧
      (faceBoundaryGraph
        (rlc_twoChannelFullReachSet gamma gamma' omega)).Adj f g ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  classical
  obtain ⟨p, q, hpq, hpR, hqR, hp0, hq0⟩ :=
    rlc_twoChannelFullReachSet_axis_boundary_of_failure
      gamma gamma' omega hno
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces hpq.1
  have hfg : (faceBoundaryGraph
      (rlc_twoChannelFullReachSet gamma gamma' omega)).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact hpq.2
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph
    (rlc_twoChannelFullReachSet gamma gamma' omega)
    (rlc_twoChannelFullReachSet_finite gamma gamma' omega)
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph (rlc_twoChannelFullReachSet gamma gamma' omega))
      T hT (degree_faceBoundaryGraph_even
        (rlc_twoChannelFullReachSet gamma gamma' omega)) hfg
  exact ⟨p, q, f, g, u, c, hpq, hpR, hqR, hp0, hq0,
    hfg, hshared, hcyc, hedge⟩


theorem rlc_twoChannelFullReachSet_openWalk_lift {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u v : RlcConnectorVertex n}
    (hu : (u : Site 2) ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (w : (openSubgraphInduce 2
      (rlc_twoChannelFullAmbientConfig gamma gamma' omega)
      (rect (-2 * n) (2 * n) (-n) n)).Walk u v) :
    ∃ hv : (v : Site 2) ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
      ((hypercubicLattice 2).induce
        (rlc_twoChannelFullReachSet gamma gamma' omega)).Reachable
          ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction w with
  | nil => exact ⟨hu, Reachable.refl _⟩
  | @cons a b c hab p ih =>
      have habOpen : (openSubgraph 2
          (rlc_twoChannelFullAmbientConfig gamma gamma' omega)).Adj
          (a : Site 2) (b : Site 2) := hab
      have hb : (b : Site 2) ∈
          rlc_twoChannelFullReachSet gamma gamma' omega :=
        rlc_twoChannelFullReachSet_extend gamma gamma' omega hu b.2
          habOpen.1 habOpen.2
      obtain ⟨hc, hbc⟩ := ih hb
      have habReach : ((hypercubicLattice 2).induce
          (rlc_twoChannelFullReachSet gamma gamma' omega)).Adj
          ⟨a, hu⟩ ⟨b, hb⟩ := habOpen.1
      exact ⟨hc, habReach.reachable.trans hbc⟩


theorem rlc_twoChannelFullReachSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') {u v : Site 2}
    (hu : u ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hv : v ∈ rlc_twoChannelFullReachSet gamma gamma' omega) :
    ((hypercubicLattice 2).induce
      (rlc_twoChannelFullReachSet gamma gamma' omega)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  have hu0 := hu
  have hv0 := hv
  obtain ⟨_huBox, huSource⟩ := hu
  obtain ⟨_hvBox, hvSource⟩ := hv
  have hsource : (rlc_connectorRightAnchor gamma : Site 2) ∈
      rlc_twoChannelFullReachSet gamma gamma' omega :=
    ⟨(rlc_connectorRightAnchor gamma).2, Reachable.refl _⟩
  obtain ⟨hu', huLift⟩ := rlc_twoChannelFullReachSet_openWalk_lift
    gamma gamma' omega hu0 huSource.some.reverse
  obtain ⟨hv', hvLift⟩ := rlc_twoChannelFullReachSet_openWalk_lift
    gamma gamma' omega hsource hvSource.some
  have huEq :
      (⟨(rlc_connectorRightAnchor gamma : Site 2), hu'⟩ :
        rlc_twoChannelFullReachSet gamma gamma' omega) =
      ⟨(rlc_connectorRightAnchor gamma : Site 2), hsource⟩ := rfl
  have hvEq :
      (⟨v, hv'⟩ : rlc_twoChannelFullReachSet gamma gamma' omega) =
      ⟨v, hv0⟩ := rfl
  rw [huEq] at huLift
  rw [hvEq] at hvLift
  exact huLift.trans hvLift


end
end StatMech.Universality
