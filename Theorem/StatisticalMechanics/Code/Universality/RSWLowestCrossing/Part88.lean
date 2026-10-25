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
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part86
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_connectorReachSet_subset_box {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    rlc_connectorReachSet gamma gamma' omega ⊆
      rect (-2 * n) (2 * n) (-n) n := by
  rintro z ⟨hzR, _⟩
  exact hzR

theorem rlc_connectorReachSet_finite {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (rlc_connectorReachSet gamma gamma' omega).Finite :=
  (rect_finite (-2 * n) (2 * n) (-n) n).subset
    (rlc_connectorReachSet_subset_box gamma gamma' omega)


theorem rlc_rightPathVertex_mem_connectorReachSet {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {x : Site 2}
    (hx : x ∈ rlc_pathVertices gamma.1) :
    x ∈ rlc_connectorReachSet gamma gamma' omega := by
  let hxR := rlc_rightPathVertex_mem_connectorBox gamma hx
  exact ⟨hxR, x, hx, hxR,
    connectedWithin_refl
      (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (rect (-2 * n) (2 * n) (-n) n) ⟨x, hxR⟩⟩


theorem rlc_connectorReachSet_extend {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_connectorReachSet gamma gamma' omega)
    (hwR : w ∈ rect (-2 * n) (2 * n) (-n) n)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hopen : rlc_maskConfig (rlc_connectorEdges gamma gamma') omega s(v, w) = true) :
    w ∈ rlc_connectorReachSet gamma gamma' omega := by
  obtain ⟨hvR, x, hx, hxR, hxv⟩ := hv
  refine ⟨hwR, x, hx, hxR, hxv.trans ?_⟩
  have hstep :
      (openSubgraphInduce 2
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
        (rect (-2 * n) (2 * n) (-n) n)).Adj ⟨v, hvR⟩ ⟨w, hwR⟩ := by
    rw [openSubgraphInduce_adj]
    exact ⟨hadj, hopen⟩
  exact hstep.reachable


theorem rlc_leftPathVertex_not_mem_connectorReachSet_of_not_connector {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') {y : Site 2}
    (hy : y ∈ rlc_pathVertices gamma'.1) :
    y ∉ rlc_connectorReachSet gamma gamma' omega := by
  rintro ⟨hyR, x, hx, hxR, hxy⟩
  exact hno ⟨x, hx, y, hy, hxR, hyR, hxy⟩


theorem rlc_connectorReachSet_boundary_closed {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_connectorReachSet gamma gamma' omega)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hw : w ∉ rlc_connectorReachSet gamma gamma' omega) :
    rlc_maskConfig (rlc_connectorEdges gamma gamma') omega s(v, w) = false := by
  by_cases hwR : w ∈ rect (-2 * n) (2 * n) (-n) n
  · by_contra hopen
    rw [Bool.not_eq_false] at hopen
    exact hw (rlc_connectorReachSet_extend gamma gamma' omega hv hwR hadj hopen)
  · have hnotU : s(v, w) ∉ rlc_connectorEdges gamma gamma' := by
      intro he
      simp only [rlc_connectorEdges, Finset.mem_filter] at he
      rw [mem_edgesWithinFinset] at he
      obtain ⟨x, hx, y, hy, hxy⟩ := he.1
      have hbox : w ∈ rlc_connectorBox n := by
        rw [Sym2.eq_iff] at hxy
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hy
        · exact hx
      exact hwR (by simpa [rlc_connectorBox] using hbox)
    simp [rlc_maskConfig, hnotU]


theorem rlc_connectorReachSet_boundary_dual_open {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hv : v ∈ rlc_connectorReachSet gamma gamma' omega)
    (hadj : (hypercubicLattice 2).Adj v w)
    (hw : w ∉ rlc_connectorReachSet gamma gamma' omega) :
    dualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (crossEdge s(v, w)) = true :=
  (isClosed_iff_dualEdge_isOpen
    (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega) s(v, w)).mp
    (rlc_connectorReachSet_boundary_closed gamma gamma' omega hv hadj hw)


theorem rlc_connectorReachSet_edgeBoundary_closed {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hvw : (v, w) ∈ edgeBoundary 2
      (rlc_connectorReachSet gamma gamma' omega)) :
    rlc_maskConfig (rlc_connectorEdges gamma gamma') omega s(v, w) = false := by
  obtain ⟨hadj, hsplit⟩ := hvw
  by_cases hv : v ∈ rlc_connectorReachSet gamma gamma' omega
  · exact rlc_connectorReachSet_boundary_closed gamma gamma' omega hv hadj
      (hsplit.mp hv)
  · have hw : w ∈ rlc_connectorReachSet gamma gamma' omega := by
      by_contra hw
      exact hv (hsplit.mpr hw)
    rw [Sym2.eq_swap]
    exact rlc_connectorReachSet_boundary_closed gamma gamma' omega hw hadj.symm hv

theorem rlc_connectorReachSet_edgeBoundary_dual_open {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {v w : Site 2}
    (hvw : (v, w) ∈ edgeBoundary 2
      (rlc_connectorReachSet gamma gamma' omega)) :
    dualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (crossEdge s(v, w)) = true :=
    (isClosed_iff_dualEdge_isOpen
    (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega) s(v, w)).mp
    (rlc_connectorReachSet_edgeBoundary_closed gamma gamma' omega hvw)


theorem rlc_faceBoundaryWalk_edges_dual_open {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_connectorReachSet gamma gamma' omega)).Walk u v)
    (hfg : s(f, g) ∈ c.edges) :
    dualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (crossEdge (sharedPrimalEdge f g)) = true := by
  have hadj : (faceBoundaryGraph
      (rlc_connectorReachSet gamma gamma' omega)).Adj f g :=
    c.adj_of_mem_edges hfg
  have hbd : bdEdge (rlc_connectorReachSet gamma gamma' omega)
      (sharedPrimalEdge f g) :=
    faceBoundaryWalk_edges_bdEdge
      (rlc_connectorReachSet gamma gamma' omega) c hfg
  obtain ⟨p, q, hpq, hadjPQ⟩ :=
    sharedPrimalEdge_isLatticeEdge hadj.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_connectorReachSet gamma gamma' omega) := by
    refine ⟨hadjPQ, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hbd
  rw [hpq]
  exact rlc_connectorReachSet_edgeBoundary_dual_open
    gamma gamma' omega hpqBoundary


theorem rlc_faceBoundaryGraph_le_openFaceDual {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega) ≤
      openSubgraph 2 (fci_faceDualConfig
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)) := by
  intro f g hfg
  obtain ⟨p, q, hpq, hadjPQ⟩ :=
    sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈ edgeBoundary 2
      (rlc_connectorReachSet gamma gamma' omega) := by
    refine ⟨hadjPQ, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hclosed := rlc_connectorReachSet_edgeBoundary_closed
    gamma gamma' omega hpqBoundary
  refine ⟨hfg.1, ?_⟩
  rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1, hpq]
  simpa using hclosed


theorem rlc_connectorReachSet_edgeBoundary_nonempty {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    (edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega)).Nonempty := by
  let v : Site 2 := gamma.1.2.1
  let w : Site 2 := v + ![1, 0]
  have hvPath : v ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨v, by simpa [v] using rightSide_subset gamma.1.2.1.2⟩,
      gamma.1.2.2.1.end_mem_support, rfl⟩
  have hv : v ∈ rlc_connectorReachSet gamma gamma' omega :=
    rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hvPath
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
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    rw [hw0, hw1]
    simp
  have hw : w ∉ rlc_connectorReachSet gamma gamma' omega := by
    intro hwReach
    have hwR := rlc_connectorReachSet_subset_box gamma gamma' omega hwReach
    rw [mem_rect] at hwR
    have : w 0 = 2 * n + 1 := by
      rw [hw0, hvx]
    omega
  exact ⟨(v, w), hadj, iff_of_true hv hw⟩


theorem rlc_connectorReachSet_dualCircuit {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    ∃ (u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_connectorReachSet gamma gamma' omega)).Walk u u), c.IsCycle := by
  obtain ⟨⟨v, w⟩, hvw⟩ :=
    rlc_connectorReachSet_edgeBoundary_nonempty gamma gamma' omega
  exact exists_dualCircuit_of_finite_of_edgeBoundary
    (rlc_connectorReachSet gamma gamma' omega)
    (rlc_connectorReachSet_finite gamma gamma' omega) hvw


theorem rlc_walk_mem_edgeBoundary_edges (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hx : x ∈ S) (hy : y ∉ S) :
    ∃ u v, (u, v) ∈ edgeBoundary 2 S ∧ s(u, v) ∈ w.edges := by
  classical
  induction w with
  | nil => exact absurd hx hy
  | @cons a b c hab p ih =>
    by_cases hb : b ∈ S
    · obtain ⟨u, v, huv, he⟩ := ih hb hy
      exact ⟨u, v, huv, by simp [he]⟩
    · exact ⟨a, b, ⟨hab, by simp [hx, hb]⟩, by simp⟩


theorem rlc_connectorReachSet_axis_boundary {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    ∃ p q : Site 2,
      (p, q) ∈ edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega) ∧
      p ∈ rect (-2 * n) (2 * n) (-n) n ∧
      q ∈ rect (-2 * n) (2 * n) (-n) n ∧
      p 0 = 0 ∧ q 0 = 0 := by
  let x : Site 2 := gamma.1.1
  let y : Site 2 := gamma'.1.2.1
  have hxPath : x ∈ rlc_pathVertices gamma.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨x, leftSide_subset gamma.1.1.2⟩,
      gamma.1.2.2.1.start_mem_support, rfl⟩
  have hyPath : y ∈ rlc_pathVertices gamma'.1 := by
    simp only [rlc_pathVertices, Finset.mem_image, List.mem_toFinset]
    exact ⟨⟨y, rightSide_subset gamma'.1.2.1.2⟩,
      gamma'.1.2.2.1.end_mem_support, rfl⟩
  have hxReach : x ∈ rlc_connectorReachSet gamma gamma' omega :=
    rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hxPath
  have hyNot : y ∉ rlc_connectorReachSet gamma gamma' omega :=
    rlc_leftPathVertex_not_mem_connectorReachSet_of_not_connector
      gamma gamma' omega hno hyPath
  have hx0 : x 0 = 0 := gamma.1.1.2.2
  have hy0 : y 0 = 0 := gamma'.1.2.1.2.2
  have hxy0 : x = ![0, x 1] := by
    ext i
    fin_cases i <;> simp [hx0]
  have hyy0 : y = ![0, y 1] := by
    ext i
    fin_cases i <;> simp [hy0]
  let w : (hypercubicLattice 2).Walk x y :=
    (sw_vertSeg 0 (x 1) (y 1)).copy hxy0.symm hyy0.symm
  obtain ⟨p, q, hpq, hpqEdge⟩ :=
    rlc_walk_mem_edgeBoundary_edges
      (rlc_connectorReachSet gamma gamma' omega) w hxReach hyNot
  have hpSupp : p ∈ w.support := w.fst_mem_support_of_mem_edges hpqEdge
  have hqSupp : q ∈ w.support := w.snd_mem_support_of_mem_edges hpqEdge
  have hsupport (z : Site 2) (hz : z ∈ w.support) :
      ∃ t : ℤ, t ∈ Set.uIcc (x 1) (y 1) ∧ z = ![0, t] := by
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


theorem rlc_connectorReachSet_axis_anchored_dualCircuit {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    ∃ (p q f g u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_connectorReachSet gamma gamma' omega)).Walk u u),
      (p, q) ∈ edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega) ∧
      p ∈ rect (-2 * n) (2 * n) (-n) n ∧
      q ∈ rect (-2 * n) (2 * n) (-n) n ∧
      p 0 = 0 ∧ q 0 = 0 ∧
      (faceBoundaryGraph
        (rlc_connectorReachSet gamma gamma' omega)).Adj f g ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges := by
  classical
  obtain ⟨p, q, hpq, hpR, hqR, hp0, hq0⟩ :=
    rlc_connectorReachSet_axis_boundary gamma gamma' omega hno
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces hpq.1
  have hfg : (faceBoundaryGraph
      (rlc_connectorReachSet gamma gamma' omega)).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact hpq.2
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph
    (rlc_connectorReachSet gamma gamma' omega)
    (rlc_connectorReachSet_finite gamma gamma' omega)
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      (faceBoundaryGraph (rlc_connectorReachSet gamma gamma' omega))
      T hT (degree_faceBoundaryGraph_even
        (rlc_connectorReachSet gamma gamma' omega)) hfg
  exact ⟨p, q, f, g, u, c, hpq, hpR, hqR, hp0, hq0,
    hfg, hshared, hcyc, hedge⟩


theorem rlc_connectorReachSet_axis_anchored_openDualCircuit {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    ∃ (p q f g u : Site 2)
      (c : (faceBoundaryGraph
        (rlc_connectorReachSet gamma gamma' omega)).Walk u u),
      (p, q) ∈ edgeBoundary 2 (rlc_connectorReachSet gamma gamma' omega) ∧
      p ∈ rect (-2 * n) (2 * n) (-n) n ∧
      q ∈ rect (-2 * n) (2 * n) (-n) n ∧
      p 0 = 0 ∧ q 0 = 0 ∧
      (faceBoundaryGraph
        (rlc_connectorReachSet gamma gamma' omega)).Adj f g ∧
      sharedPrimalEdge f g = s(p, q) ∧
      c.IsCycle ∧ s(f, g) ∈ c.edges ∧
      ∀ a b : Site 2, s(a, b) ∈ c.edges →
        dualConfig (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
          (crossEdge (sharedPrimalEdge a b)) = true := by
  obtain ⟨p, q, f, g, u, c, hpq, hpR, hqR, hp0, hq0,
      hfg, hshared, hcyc, hedge⟩ :=
    rlc_connectorReachSet_axis_anchored_dualCircuit gamma gamma' omega hno
  refine ⟨p, q, f, g, u, c, hpq, hpR, hqR, hp0, hq0,
    hfg, hshared, hcyc, hedge, ?_⟩
  intro a b hab
  exact rlc_faceBoundaryWalk_edges_dual_open gamma gamma' omega c hab


theorem rlc_connectorReachSet_openFaceDualCircuit {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    ∃ (u : Site 2)
      (c : (openSubgraph 2 (fci_faceDualConfig
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega))).Walk u u),
      c.IsCycle := by
  obtain ⟨_p, _q, _f, _g, u, c, _hpq, _hpR, _hqR, _hp0, _hq0,
      _hfg, _hshared, hcyc, _hedge⟩ :=
    rlc_connectorReachSet_axis_anchored_dualCircuit gamma gamma' omega hno
  let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma' omega
  exact ⟨u, c.mapLe hle, hcyc.mapLe hle⟩


end Universality
end StatMech
