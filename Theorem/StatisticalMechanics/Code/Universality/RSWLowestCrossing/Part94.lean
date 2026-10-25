/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part92
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_axisGapReachSet_subset_box {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_axisGapReachSet G omega ⊆
      rect (-2 * n) (2 * n) (-n) n := by
  rintro z ⟨hzR, _⟩
  exact hzR

theorem rlc_axisGapReachSet_finite {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (rlc_axisGapReachSet G omega).Finite :=
  (rect_finite (-2 * n) (2 * n) (-n) n).subset
    (rlc_axisGapReachSet_subset_box G omega)

theorem rlc_rightPathVertex_mem_axisGapReachSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {x : Site 2}
    (hx : x ∈ rlc_pathVertices gamma.1) :
    x ∈ rlc_axisGapReachSet G omega := by
  let hxR := rlc_rightPathVertex_mem_connectorBox gamma hx
  exact ⟨hxR, x, hx, hxR,
    connectedWithin_refl
      (rlc_maskConfig (rlc_axisGapEdges G) omega)
      (rect (-2 * n) (2 * n) (-n) n) ⟨x, hxR⟩⟩

theorem rlc_axisGapReachSet_extend {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_axisGapReachSet G omega)
    (hwR : w ∈ rect (-2 * n) (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hopen : rlc_maskConfig (rlc_axisGapEdges G) omega s(v, w) = true) :
    w ∈ rlc_axisGapReachSet G omega := by
  obtain ⟨hvR, x, hx, hxR, hxv⟩ := hv
  refine ⟨hwR, x, hx, hxR, hxv.trans ?_⟩
  have hstep :
      (openSubgraphInduce 2
        (rlc_maskConfig (rlc_axisGapEdges G) omega)
        (rect (-2 * n) (2 * n) (-n) n)).Adj ⟨v, hvR⟩ ⟨w, hwR⟩ := by
    rw [openSubgraphInduce_adj]
    exact ⟨hadj, hopen⟩
  exact hstep.reachable

theorem rlc_leftPathVertex_not_mem_axisGapReachSet_of_failure {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_axisGapConnectorEvent G) {y : Site 2}
    (hy : y ∈ rlc_pathVertices gamma'.1) :
    y ∉ rlc_axisGapReachSet G omega := by
  rintro ⟨hyR, x, hx, hxR, hxy⟩
  exact hno ⟨x, hx, y, hy, hxR, hyR, hxy⟩


theorem rlc_axisGapEdges_endpoints_mem_box {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) {v w : Site 2}
    (he : s(v, w) ∈ rlc_axisGapEdges G) :
    v ∈ rect (-2 * n) (2 * n) (-n) n ∧
      w ∈ rect (-2 * n) (2 * n) (-n) n := by
  rw [rlc_axisGapEdges, Finset.mem_union] at he
  rcases he with he | he
  · simp only [Finset.mem_filter] at he
    rw [mem_edgesWithinFinset] at he
    obtain ⟨x, hx, y, hy, hxy⟩ := he.1
    rw [Sym2.eq_iff] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [rlc_connectorBox] using And.intro hx hy
    · simpa [rlc_connectorBox] using And.intro hy hx
  · have heq : s(v, w) = s(G.lowerVertex, G.seedVertex) := by
      simpa [RlcAxisBarrierGap.firstEdge] using he
    have hlower := rlc_rightPathVertex_mem_connectorBox
      gamma G.lowerVertex_mem_right
    have hseed := G.seedVertex_mem_box_of_lt hn hlt
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hlower, by simpa [rlc_connectorBox] using hseed⟩
    · exact ⟨by simpa [rlc_connectorBox] using hseed, hlower⟩


theorem rlc_axisGapReachSet_boundary_closed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_axisGapReachSet G omega)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hw : w ∉ rlc_axisGapReachSet G omega) :
    rlc_maskConfig (rlc_axisGapEdges G) omega s(v, w) = false := by
  by_cases hwR : w ∈ rect (-2 * n) (2 * n) (-n) n
  · by_contra hopen
    rw [Bool.not_eq_false] at hopen
    exact hw (rlc_axisGapReachSet_extend G omega hv hwR hadj hopen)
  · have hnotU : s(v, w) ∉ rlc_axisGapEdges G := by
      intro he
      exact hwR (rlc_axisGapEdges_endpoints_mem_box G hn hlt he).2
    simp [rlc_maskConfig, hnotU]

theorem rlc_axisGapReachSet_edgeBoundary_closed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hvw : (v, w) ∈ edgeBoundary 2 (rlc_axisGapReachSet G omega)) :
    rlc_maskConfig (rlc_axisGapEdges G) omega s(v, w) = false := by
  obtain ⟨hadj, hsplit⟩ := hvw
  by_cases hv : v ∈ rlc_axisGapReachSet G omega
  · exact rlc_axisGapReachSet_boundary_closed G hn hlt omega hv hadj
      (hsplit.mp hv)
  · have hw : w ∈ rlc_axisGapReachSet G omega := by
      by_contra hw
      exact hv (hsplit.mpr hw)
    rw [Sym2.eq_swap]
    exact rlc_axisGapReachSet_boundary_closed G hn hlt omega hw hadj.symm hv


theorem rlc_axisGapFaceBoundaryGraph_le_openFaceDual {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    faceBoundaryGraph (rlc_axisGapReachSet G omega) ≤
      openSubgraph 2 (fci_faceDualConfig
        (rlc_maskConfig (rlc_axisGapEdges G) omega)) := by
  intro f g hfg
  obtain ⟨p, q, hpq, hadjPQ⟩ :=
    sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_axisGapReachSet G omega) := by
    refine ⟨hadjPQ, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hclosed := rlc_axisGapReachSet_edgeBoundary_closed
    G hn hlt omega hpqBoundary
  refine ⟨hfg.1, ?_⟩
  rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1, hpq]
  simpa using hclosed


theorem rlc_axisGapReachSet_axis_boundary {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_axisGapConnectorEvent G) :
    ∃ p q : Site 2,
      (p, q) ∈ edgeBoundary 2 (rlc_axisGapReachSet G omega) ∧
      p 0 = 0 ∧ q 0 = 0 := by
  have hlower : G.lowerVertex ∈ rlc_axisGapReachSet G omega :=
    rlc_rightPathVertex_mem_axisGapReachSet G omega G.lowerVertex_mem_right
  have hupper : G.upperVertex ∉ rlc_axisGapReachSet G omega :=
    rlc_leftPathVertex_not_mem_axisGapReachSet_of_failure
      G omega hno G.upperVertex_mem_left
  let w : (hypercubicLattice 2).Walk G.lowerVertex G.upperVertex :=
    sw_vertSeg 0 G.lower G.upper
  obtain ⟨p, q, hpq, hpqEdge⟩ :=
    rlc_walk_mem_edgeBoundary_edges
      (rlc_axisGapReachSet G omega) w hlower hupper
  have hpSupp : p ∈ w.support := w.fst_mem_support_of_mem_edges hpqEdge
  have hqSupp : q ∈ w.support := w.snd_mem_support_of_mem_edges hpqEdge
  have haxis (z : Site 2) (hz : z ∈ w.support) : z 0 = 0 := by
    change z ∈ (sw_vertSeg 0 G.lower G.upper).support at hz
    rw [sw_vertSeg_mem_support] at hz
    obtain ⟨t, _ht, rfl⟩ := hz
    simp
  exact ⟨p, q, hpq, haxis p hpSupp, haxis q hqSupp⟩


theorem rlc_axisGapReachSet_axis_anchored_dualCircuit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_axisGapConnectorEvent G) :
    ∃ (p q f g u : Site 2)
      (c : (faceBoundaryGraph (rlc_axisGapReachSet G omega)).Walk u u),
      (p, q) ∈ edgeBoundary 2 (rlc_axisGapReachSet G omega) ∧
      p 0 = 0 ∧ q 0 = 0 ∧
      (faceBoundaryGraph (rlc_axisGapReachSet G omega)).Adj f g ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  classical
  obtain ⟨p, q, hpq, hp0, hq0⟩ :=
    rlc_axisGapReachSet_axis_boundary G omega hno
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces hpq.1
  have hfg : (faceBoundaryGraph
      (rlc_axisGapReachSet G omega)).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact hpq.2
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph
    (rlc_axisGapReachSet G omega) (rlc_axisGapReachSet_finite G omega)
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph (rlc_axisGapReachSet G omega)) T hT
      (degree_faceBoundaryGraph_even (rlc_axisGapReachSet G omega)) hfg
  exact ⟨p, q, f, g, u, c, hpq, hp0, hq0,
    hfg, hshared, hcyc, hedge⟩


theorem rlc_axisGapReachSet_openFaceDualCircuit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_axisGapConnectorEvent G) :
    ∃ (p q f g u : Site 2)
      (c : (openSubgraph 2 (fci_faceDualConfig
        (rlc_maskConfig (rlc_axisGapEdges G) omega))).Walk u u),
      p 0 = 0 ∧ q 0 = 0 ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  obtain ⟨p, q, f, g, u, c, _hpq, hp0, hq0, _hfg,
      hshared, hcyc, hedge⟩ :=
    rlc_axisGapReachSet_axis_anchored_dualCircuit G omega hno
  let hle := rlc_axisGapFaceBoundaryGraph_le_openFaceDual G hn hlt omega
  refine ⟨p, q, f, g, u, c.mapLe hle, hp0, hq0, hshared,
    hcyc.mapLe hle, ?_⟩
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  exact hedge


theorem rlc_axisGapReachSet_reflectedOpenDualCircuit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_axisGapConnectorEvent G) :
    ∃ (p q f g u : Site 2)
      (c : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_maskConfig (rlc_axisGapEdges G) omega))).Walk
          (rlc_dualReflect u) (rlc_dualReflect u)),
      p 0 = 0 ∧ q 0 = 0 ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧
      s(rlc_dualReflect f, rlc_dualReflect g) ∈ c.edges := by
  obtain ⟨p, q, f, g, u, c, hp0, hq0, hshared, hcyc, hedge⟩ :=
    rlc_axisGapReachSet_openFaceDualCircuit G hn hlt omega hno
  let hom := rlc_dualReflectOpenHom
    (rlc_maskConfig (rlc_axisGapEdges G) omega)
  refine ⟨p, q, f, g, u, rlc_dualReflectOpenWalk _ c,
    hp0, hq0, hshared, rlc_dualReflectOpenWalk_isCycle _ hcyc, ?_⟩
  have hEdges : (c.map hom).edges =
      c.edges.map (Sym2.map hom) :=
    SimpleGraph.Walk.edges_map hom c
  have hmapped : Sym2.map hom s(f, g) ∈
      c.edges.map (Sym2.map hom) :=
    List.mem_map_of_mem hedge
  have hedgeEq : Sym2.map hom s(f, g) =
      s(rlc_dualReflect f, rlc_dualReflect g) := by
    rfl
  change s(rlc_dualReflect f, rlc_dualReflect g) ∈ (c.map hom).edges
  exact hedgeEq ▸ hEdges.symm ▸ hmapped


theorem rlc_axisGapConnector_half_of_dual_reflection {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (hdual : ∀ omega : ConfigSpace (Sym2 (Site 2)),
      omega ∉ rlc_axisGapConnectorEvent G →
      rlc_dualReflectConfig omega ∈ rlc_axisGapConnectorEvent G) :
    (1 : ℝ) / 2 ≤
      rba_selfDualMeasure.real (rlc_axisGapConnectorEvent G) := by
  apply rlc_connector_half_of_dual_reflection rba_selfDualMeasure
    rlc_dualReflectConfig rlc_dualReflectConfig_measurePreserving
    (rlc_axisGapConnectorEvent G)
    (rlc_axisGapConnectorEvent_measurableSet G)
  intro omega hno
  exact hdual omega hno


theorem rlc_adaptiveConnector_half_of_dual_reflection {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hdual : ∀ (G : RlcAxisBarrierGap gamma gamma')
      (_hlt : G.lower + 1 < G.upper)
      (omega : ConfigSpace (Sym2 (Site 2))),
      omega ∉ rlc_axisGapConnectorEvent G →
      rlc_dualReflectConfig omega ∈ rlc_axisGapConnectorEvent G) :
    (1 : ℝ) / 2 ≤
      rba_selfDualMeasure.real
        (rlc_adaptiveConnectorEvent gamma gamma') := by
  apply rlc_adaptiveConnector_half_of_nonadjacent gamma gamma'
  intro G hlt
  exact rlc_axisGapConnector_half_of_dual_reflection G
    (hdual G hlt)


end Universality
end StatMech
