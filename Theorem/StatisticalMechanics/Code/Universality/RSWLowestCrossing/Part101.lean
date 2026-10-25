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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part99
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_mixedWiredReachSet_subset_box {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_mixedWiredReachSet G omega ⊆
      rect (-2 * n) (2 * n) (-n) n := by
  rintro z ⟨hzR, _⟩
  exact hzR

theorem rlc_mixedWiredReachSet_finite {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (rlc_mixedWiredReachSet G omega).Finite :=
  (rect_finite (-2 * n) (2 * n) (-n) n).subset
    (rlc_mixedWiredReachSet_subset_box G omega)

theorem RlcAxisBarrierGap.lowerVertex_mem_mixedWiredReachSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    G.lowerVertex ∈ rlc_mixedWiredReachSet G omega := by
  exact ⟨rlc_rightPathVertex_mem_connectorBox gamma G.lowerVertex_mem_right,
    connectedWithin_refl _ _ _⟩


theorem rlc_rightPathVertex_mem_mixedWiredReachSet {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {x : Site 2}
    (hx : x ∈ rlc_pathVertices gamma.1) :
    x ∈ rlc_mixedWiredReachSet G omega := by
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  have hopen : eta ∈ rlc_pathOpen gamma.1 :=
    rlc_wiredConnectorConfig_rightPathOpen gamma gamma'
      (rlc_mixedAxisGapEdges G) omega
  obtain ⟨hlR, hstartLower⟩ :=
    rlc_pathOpen_connected_start gamma.1 eta hopen G.lowerVertex_mem_right
  obtain ⟨hxR, hstartX⟩ := rlc_pathOpen_connected_start gamma.1 eta hopen hx
  refine ⟨rlc_rightPathVertex_mem_connectorBox gamma hx, ?_⟩
  have hsub : rect 0 (2 * n) (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  exact (StatMech.RSW.Strip.connectedWithin_mono_set eta hsub
    hstartLower).symm.trans
      (StatMech.RSW.Strip.connectedWithin_mono_set eta hsub hstartX)


theorem rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    {y : Site 2} (hy : y ∈ rlc_pathVertices gamma'.1) :
    y ∉ rlc_mixedWiredReachSet G omega := by
  rintro ⟨hyR, hlowerY⟩
  let eta := rlc_wiredConnectorConfig gamma gamma'
    (rlc_mixedAxisGapEdges G) omega
  have hopen : eta ∈ rlc_pathOpen gamma'.1 :=
    rlc_wiredConnectorConfig_leftPathOpen gamma gamma'
      (rlc_mixedAxisGapEdges G) omega
  obtain ⟨hySmall, hstartY⟩ :=
    rlc_pathOpen_connected_start gamma'.1 eta hopen hy
  obtain ⟨huSmall, hstartUpper⟩ :=
    rlc_pathOpen_connected_start gamma'.1 eta hopen G.upperVertex_mem_left
  have hsub : rect (-2 * n) 0 (-n) n ⊆
      rect (-2 * n) (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  have hyUpper : ConnectedWithin 2 eta
      (rect (-2 * n) (2 * n) (-n) n) ⟨y, hyR⟩
      ⟨G.upperVertex,
        rlc_leftPathVertex_mem_connectorBox gamma' G.upperVertex_mem_left⟩ :=
    (StatMech.RSW.Strip.connectedWithin_mono_set eta hsub hstartY).symm.trans
      (StatMech.RSW.Strip.connectedWithin_mono_set eta hsub hstartUpper)
  exact hno (hlowerY.trans hyUpper)


theorem rlc_mixedWiredReachSet_axis_boundary {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ p q : Site 2,
      (p, q) ∈ edgeBoundary 2 (rlc_mixedWiredReachSet G omega) ∧
      p 0 = 0 ∧ q 0 = 0 := by
  have hlower := G.lowerVertex_mem_mixedWiredReachSet omega
  have hupper : G.upperVertex ∉ rlc_mixedWiredReachSet G omega :=
    rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
      G omega hno G.upperVertex_mem_left
  let w : (hypercubicLattice 2).Walk G.lowerVertex G.upperVertex :=
    sw_vertSeg 0 G.lower G.upper
  obtain ⟨p, q, hpq, hpqEdge⟩ :=
    rlc_walk_mem_edgeBoundary_edges
      (rlc_mixedWiredReachSet G omega) w hlower hupper
  have hpSupp : p ∈ w.support := w.fst_mem_support_of_mem_edges hpqEdge
  have hqSupp : q ∈ w.support := w.snd_mem_support_of_mem_edges hpqEdge
  have haxis (z : Site 2) (hz : z ∈ w.support) : z 0 = 0 := by
    change z ∈ (sw_vertSeg 0 G.lower G.upper).support at hz
    rw [sw_vertSeg_mem_support] at hz
    obtain ⟨t, _ht, rfl⟩ := hz
    simp
  exact ⟨p, q, hpq, haxis p hpSupp, haxis q hqSupp⟩


theorem rlc_mixedWiredReachSet_verticalGap_boundary {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ t : ℤ, G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      ((![0, t], ![0, t + 1]) ∈
        edgeBoundary 2 (rlc_mixedWiredReachSet G omega)) := by
  classical
  let S := rlc_mixedWiredReachSet G omega
  have hlower : ![0, G.lower] ∈ S := by
    simpa [S, RlcAxisBarrierGap.lowerVertex] using
      G.lowerVertex_mem_mixedWiredReachSet omega
  have hupper : ![0, G.upper] ∉ S := by
    simpa [S, RlcAxisBarrierGap.upperVertex] using
      (rlc_leftPathVertex_not_mem_mixedWiredReachSet_of_failure
        G omega hno G.upperVertex_mem_left)
  let A : Finset ℤ := (Finset.Icc G.lower G.upper).filter
    (fun t => ![0, t] ∈ S)
  have hlowerA : G.lower ∈ A := by
    simp [A, hlower, le_of_lt G.lower_lt_upper]
  have hA : A.Nonempty := ⟨G.lower, hlowerA⟩
  let t := A.max' hA
  have htA : t ∈ A := A.max'_mem hA
  have htBounds : G.lower ≤ t ∧ t ≤ G.upper := by
    simpa [A] using (Finset.mem_filter.mp htA).1
  have htS : ![0, t] ∈ S := (Finset.mem_filter.mp htA).2
  have htlt : t < G.upper := by
    apply lt_of_le_of_ne htBounds.2
    intro h
    exact hupper (h ▸ htS)
  have hsuccNot : ![0, t + 1] ∉ S := by
    intro hsucc
    have hsuccA : t + 1 ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hsucc⟩
    have hmax := A.le_max' (t + 1) hsuccA
    change t + 1 ≤ t at hmax
    omega
  have hadj : (hypercubicLattice 2).Adj
      (![0, t] : Site 2) ![0, t + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ⟨t, htBounds.1, htlt, htS, hsuccNot,
    ⟨hadj, iff_of_true htS hsuccNot⟩⟩

theorem rlc_mem_connectorBox_flipX {n : ℤ} (z : Site 2) :
    z ∈ rect (-2 * n) (2 * n) (-n) n ↔
      rlc_flipX z ∈ rect (-2 * n) (2 * n) (-n) n := by
  have hzero : rlc_flipX z 0 = -z 0 := rfl
  have hone : rlc_flipX z 1 = z 1 := rfl
  simp only [mem_rect, hzero, hone]
  omega

theorem rlc_reflectedRightPathEdge_endpoint_mem_box {n : ℤ}
    (gamma : RlcRightDiagonalPath n) {e : Sym2 (Site 2)}
    (he : e ∈ rlc_reflectedPathEdges gamma.1) {z : Site 2}
    (hz : z ∈ e) : z ∈ rect (-2 * n) (2 * n) (-n) n := by
  obtain ⟨e0, he0, heq⟩ := Finset.mem_image.mp he
  induction e0 using Sym2.inductionOn with
  | _ x y =>
    have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he0
    have hxR := rlc_rightPathVertex_mem_connectorBox gamma hends.1
    have hyR := rlc_rightPathVertex_mem_connectorBox gamma hends.2
    have heq' : e = s(rlc_flipX x, rlc_flipX y) := by
      simpa [Sym2.map_mk] using heq.symm
    rw [heq', Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact (rlc_mem_connectorBox_flipX x).mp hxR
    · exact (rlc_mem_connectorBox_flipX y).mp hyR

theorem rlc_reflectedLeftPathEdge_endpoint_mem_box {n : ℤ}
    (gamma' : RlcLeftDiagonalPath n) {e : Sym2 (Site 2)}
    (he : e ∈ rlc_reflectedPathEdges gamma'.1) {z : Site 2}
    (hz : z ∈ e) : z ∈ rect (-2 * n) (2 * n) (-n) n := by
  obtain ⟨e0, he0, heq⟩ := Finset.mem_image.mp he
  induction e0 using Sym2.inductionOn with
  | _ x y =>
    have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 he0
    have hxR := rlc_leftPathVertex_mem_connectorBox gamma' hends.1
    have hyR := rlc_leftPathVertex_mem_connectorBox gamma' hends.2
    have heq' : e = s(rlc_flipX x, rlc_flipX y) := by
      simpa [Sym2.map_mk] using heq.symm
    rw [heq', Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact (rlc_mem_connectorBox_flipX x).mp hxR
    · exact (rlc_mem_connectorBox_flipX y).mp hyR


theorem rlc_mixedAxisGapEdges_endpoints_mem_box {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper) {v w : Site 2}
    (he : s(v, w) ∈ rlc_mixedAxisGapEdges G) :
    v ∈ rect (-2 * n) (2 * n) (-n) n ∧
      w ∈ rect (-2 * n) (2 * n) (-n) n := by
  have heUnion := (Finset.mem_sdiff.mp he).1
  simp only [Finset.mem_union] at heUnion
  rcases heUnion with heUnion | heLeft
  · rcases heUnion with heGap | heRight
    · exact rlc_axisGapEdges_endpoints_mem_box G hn hlt heGap
    · exact ⟨rlc_reflectedRightPathEdge_endpoint_mem_box gamma heRight
        (Sym2.mem_mk_left v w),
        rlc_reflectedRightPathEdge_endpoint_mem_box gamma heRight
          (Sym2.mem_mk_right v w)⟩
  · exact ⟨rlc_reflectedLeftPathEdge_endpoint_mem_box gamma' heLeft
      (Sym2.mem_mk_left v w),
      rlc_reflectedLeftPathEdge_endpoint_mem_box gamma' heLeft
        (Sym2.mem_mk_right v w)⟩

theorem rlc_exposedPathEdges_endpoints_mem_box {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {v w : Site 2}
    (he : s(v, w) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    v ∈ rect (-2 * n) (2 * n) (-n) n ∧
      w ∈ rect (-2 * n) (2 * n) (-n) n := by
  rw [Finset.mem_union] at he
  rcases he with he | he
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he
    exact ⟨rlc_rightPathVertex_mem_connectorBox gamma hends.1,
      rlc_rightPathVertex_mem_connectorBox gamma hends.2⟩
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 he
    exact ⟨rlc_leftPathVertex_mem_connectorBox gamma' hends.1,
      rlc_leftPathVertex_mem_connectorBox gamma' hends.2⟩

theorem rlc_mixedWiredReachSet_extend {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_mixedWiredReachSet G omega)
    (hwR : w ∈ rect (-2 * n) (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hopen : rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega s(v, w) = true) :
    w ∈ rlc_mixedWiredReachSet G omega := by
  obtain ⟨hvR, hlowerV⟩ := hv
  refine ⟨hwR, hlowerV.trans ?_⟩
  have hstep : (openSubgraphInduce 2
      (rlc_wiredConnectorConfig gamma gamma'
        (rlc_mixedAxisGapEdges G) omega)
      (rect (-2 * n) (2 * n) (-n) n)).Adj ⟨v, hvR⟩ ⟨w, hwR⟩ := by
    rw [openSubgraphInduce_adj]
    exact ⟨hadj, hopen⟩
  exact hstep.reachable


theorem rlc_mixedWiredReachSet_boundary_closed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_mixedWiredReachSet G omega)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hw : w ∉ rlc_mixedWiredReachSet G omega) :
    rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega s(v, w) = false := by
  by_cases hwR : w ∈ rect (-2 * n) (2 * n) (-n) n
  · by_contra hopen
    rw [Bool.not_eq_false] at hopen
    exact hw (rlc_mixedWiredReachSet_extend G omega hv hwR hadj hopen)
  · have hnotPaths : s(v, w) ∉
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
      intro he
      exact hwR (rlc_exposedPathEdges_endpoints_mem_box he).2
    have hnotU : s(v, w) ∉ rlc_mixedAxisGapEdges G := by
      intro he
      exact hwR (rlc_mixedAxisGapEdges_endpoints_mem_box G hn hlt he).2
    simp [rlc_wiredConnectorConfig, hnotPaths, rlc_maskConfig, hnotU]

theorem rlc_mixedWiredReachSet_edgeBoundary_closed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hvw : (v, w) ∈ edgeBoundary 2 (rlc_mixedWiredReachSet G omega)) :
    rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega s(v, w) = false := by
  obtain ⟨hadj, hsplit⟩ := hvw
  by_cases hv : v ∈ rlc_mixedWiredReachSet G omega
  · exact rlc_mixedWiredReachSet_boundary_closed G hn hlt omega hv hadj
      (hsplit.mp hv)
  · have hw : w ∈ rlc_mixedWiredReachSet G omega := by
      by_contra hw
      exact hv (hsplit.mpr hw)
    rw [Sym2.eq_swap]
    exact rlc_mixedWiredReachSet_boundary_closed G hn hlt omega hw hadj.symm hv


theorem rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    faceBoundaryGraph (rlc_mixedWiredReachSet G omega) ≤
      openSubgraph 2 (fci_faceDualConfig
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega)) := by
  intro f g hfg
  obtain ⟨p, q, hpq, hadjPQ⟩ :=
    sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_mixedWiredReachSet G omega) := by
    refine ⟨hadjPQ, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hclosed := rlc_mixedWiredReachSet_edgeBoundary_closed
    G hn hlt omega hpqBoundary
  refine ⟨hfg.1, ?_⟩
  rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1, hpq]
  simpa using hclosed


theorem rlc_mixedWiredReachSet_axis_anchored_dualCircuit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ (t : ℤ) (f g u : Site 2)
      (c : (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Walk u u),
      G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)).Adj f g ∧
      sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  classical
  obtain ⟨t, htlower, htupper, htIn, htOut, hpq⟩ :=
    rlc_mixedWiredReachSet_verticalGap_boundary G omega hno
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces hpq.1
  have hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact hpq.2
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph
    (rlc_mixedWiredReachSet G omega)
    (rlc_mixedWiredReachSet_finite G omega)
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph (rlc_mixedWiredReachSet G omega)) T hT
      (degree_faceBoundaryGraph_even (rlc_mixedWiredReachSet G omega)) hfg
  exact ⟨t, f, g, u, c, htlower, htupper, htIn, htOut,
    hfg, hshared, hcyc, hedge⟩

theorem rlc_mixedWiredReachSet_openFaceDualCircuit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ (t : ℤ) (f g u : Site 2)
      (c : (openSubgraph 2 (fci_faceDualConfig
        (rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega))).Walk u u),
      G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      (hypercubicLattice 2).Adj f g ∧
      sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  obtain ⟨t, f, g, u, c, htlower, htupper, htIn, htOut, hfg,
      hshared, hcyc, hedge⟩ :=
    rlc_mixedWiredReachSet_axis_anchored_dualCircuit G omega hno
  let hle := rlc_mixedWiredFaceBoundaryGraph_le_openFaceDual G hn hlt omega
  refine ⟨t, f, g, u, c.mapLe hle, htlower, htupper, htIn, htOut,
    hfg.1, hshared,
    hcyc.mapLe hle, ?_⟩
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  exact hedge


theorem rlc_mixedWiredReachSet_reflectedOpenDualCircuit {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ (t : ℤ) (u : Site 2)
      (c : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega))).Walk
          (rlc_dualReflect u) (rlc_dualReflect u)),
      G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      c.IsCycle ∧
      s(![-1, t + 1], ![0, t + 1]) ∈ c.edges := by
  obtain ⟨t, f, g, u, c, htlower, htupper, htIn, htOut, hfg,
      hshared, hcyc, hedge⟩ :=
    rlc_mixedWiredReachSet_openFaceDualCircuit G hn hlt omega hno
  let hom := rlc_dualReflectOpenHom
    (rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega)
  refine ⟨t, u, rlc_dualReflectOpenWalk _ c,
    htlower, htupper, htIn, htOut,
    rlc_dualReflectOpenWalk_isCycle _ hcyc, ?_⟩
  have hEdges : (c.map hom).edges = c.edges.map (Sym2.map hom) :=
    SimpleGraph.Walk.edges_map hom c
  have hmapped : Sym2.map hom s(f, g) ∈
      c.edges.map (Sym2.map hom) := List.mem_map_of_mem hedge
  have hedgeEq : Sym2.map hom s(f, g) =
      s(rlc_dualReflect f, rlc_dualReflect g) := by
    rfl
  have hreflected : s(rlc_dualReflect f, rlc_dualReflect g) =
      s(![-1, t + 1], ![0, t + 1]) :=
    rlc_reflectedEdge_eq_horizontal_of_shared_vertical hfg hshared
  change s(![-1, t + 1], ![0, t + 1]) ∈ (c.map hom).edges
  rw [← hreflected]
  exact hedgeEq ▸ hEdges.symm ▸ hmapped


theorem rlc_mixedWiredReachSet_reflectedOpenDualComplementaryArc {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ t : ℤ, G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      ∃ p : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_wiredConnectorConfig gamma gamma'
          (rlc_mixedAxisGapEdges G) omega))).Walk
          ![-1, t + 1] ![0, t + 1],
        s(![-1, t + 1], ![0, t + 1]) ∉ p.edges := by
  obtain ⟨t, u, c, htlower, htupper, htIn, htOut, hcyc, hedge⟩ :=
    rlc_mixedWiredReachSet_reflectedOpenDualCircuit G hn hlt omega hno
  let H := openSubgraph 2 (rlc_dualReflectConfig
    (rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega))
  have hreach : (H.deleteEdges
      {s(![-1, t + 1], ![0, t + 1])}).Reachable
        ![-1, t + 1] ![0, t + 1] :=
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
      (G := H)).mpr ⟨rlc_dualReflect u, c, hcyc, hedge⟩ |>.2
  obtain ⟨p, hp⟩ :=
    (SimpleGraph.reachable_deleteEdges_iff_exists_walk (G := H)).mp hreach
  exact ⟨t, htlower, htupper, htIn, htOut, p, hp⟩


theorem rlc_mixedWiredFailure_reflectedAnchor_open_raw {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ t : ℤ, G.lower ≤ t ∧ t < G.upper ∧
      rlc_dualReflectConfig omega
        s(![-1, t + 1], ![0, t + 1]) = true := by
  obtain ⟨t, htlower, htupper, htIn, htOut, hpq⟩ :=
    rlc_mixedWiredReachSet_verticalGap_boundary G omega hno
  let e : Sym2 (Site 2) := s(![0, t], ![0, t + 1])
  have hU : e ∈ rlc_mixedAxisGapEdges G := by
    exact G.verticalEdge_mem_mixedAxisGapEdges hn hlt htlower htupper
  have hnotPaths : e ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
    intro he
    rw [Finset.mem_union] at he
    rcases he with he | he
    · exact (Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_mixedAxisGapEdges G)) he hU
    · exact (Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_mixedAxisGapEdges G)) he hU
  have hclosed := rlc_mixedWiredReachSet_boundary_closed
    G hn hlt omega htIn hpq.1 htOut
  have homega : omega e = false := by
    change rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega e = false at hclosed
    rw [rlc_wiredConnectorConfig, if_neg hnotPaths,
      rlc_maskConfig, if_pos hU] at hclosed
    exact hclosed
  refine ⟨t, htlower, htupper, ?_⟩
  have hpims : rlc_pimsEdgeEquiv
      s(![-1, t + 1], ![0, t + 1]) = e := by
    simpa [e] using (rlc_pimsEdgeEquiv_horizontal (-1) (t + 1))
  rw [rlc_dualReflectConfig_eq_pims, hpims, homega]
  rfl

end Universality
end StatMech
