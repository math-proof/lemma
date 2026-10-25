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
import Structure.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_centralFace_lowestRetainedAnchoredBoundary_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    Nonempty (RlcCentralFaceLowestRetainedAnchoredBoundary
      gamma gamma' rho) := by
  classical
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  let hH := rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho
  let T := phb_boundarySupport H hH
  let L := Classical.choice
    (rlc_centralFaceLowestFilledAxisGap_of_failure
      gamma gamma' hposition rho hno)
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces L.boundary.1
  have hfg : (faceBoundaryGraph H).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact L.boundary.2
  have hconn : FaceBoundaryConnected H T := by
    simpa [H, hH, T] using
      (rlc_connectorCentralFaceFilledReachSet_faceBoundaryConnected
        gamma gamma' rho)
  have hsupp : (faceBoundaryGraph H).support ⊆ (T : Set (Site 2)) := by
    intro z hz
    simpa [T, H, hH] using hz
  have hfT : f ∈ T := by
    simpa [T, H, hH] using hfg.mem_support_left
  have hcoversComponent :
      ∀ e ∈ (faceBoundaryGraph H).edgeSet,
        e ∈ (componentGraph H f).edgeSet :=
    componentCovers_of_faceBoundaryConnected hsupp hconn hfT
  obtain ⟨c, hcTrail, hcCovers⟩ :=
    dualCircuit_of_componentCovers hsupp hfT hcoversComponent
  have hanchor : s(f, g) ∈ c.edges := by
    apply hcCovers
    rw [SimpleGraph.mem_edgeSet]
    exact hfg
  let B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho := {
    height := L.height
    firstFace := f
    secondFace := g
    contour := c
    height_lower := L.height_lower
    height_upper := L.height_upper
    axis_inside := L.axis_inside
    axis_outside := L.axis_outside
    anchor_adj := hfg
    anchor_shared := hshared
    contour_isTrail := hcTrail
    contour_covers := hcCovers
    anchor_mem := hanchor
  }
  exact ⟨{
    boundary := B
    axis_below_inside := L.axis_below_inside
  }⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_axis_boundary
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {s : Int} (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
    (hs : s < L.boundary.height) :
    ((![0, s], ![0, s + 1]) ∉ edgeBoundary 2
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) := by
  intro hboundary
  have hsIn := L.axis_below_inside s hsLower (by omega)
  have hsuccIn := L.axis_below_inside (s + 1) (by omega) (by omega)
  exact (hboundary.2.mp hsIn) hsuccIn


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_contour_axis_crossing
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {f g : Site 2} {s : Int}
    (hfg : s(f, g) ∈ L.boundary.contour.edges)
    (hshared : sharedPrimalEdge f g =
      s((![0, s] : Site 2), ![0, s + 1]))
    (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
    (hs : s < L.boundary.height) : False := by
  apply L.no_lower_axis_boundary hsLower hs
  have hbd := (L.boundary.contour.adj_of_mem_edges hfg).2
  rw [hshared, bdEdge_mk] at hbd
  exact ⟨by simp [hypercubicLattice_adj, Fin.sum_univ_two], hbd⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_reflected_axis_crossing
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {f g : Site 2} {s : Int}
    (hfg : s(f, g) ∈ L.boundary.contour.edges)
    (hreflected : s(rlc_dualReflect f, rlc_dualReflect g) =
      s((![-1, s + 1] : Site 2), ![0, s + 1]))
    (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
    (hs : s < L.boundary.height) : False := by
  have hfgAdj := L.boundary.contour.adj_of_mem_edges hfg
  have hmap := congrArg rlc_pimsEdgeEquiv hreflected
  have hshared : sharedPrimalEdge f g =
      s((![0, s] : Site 2), ![0, s + 1]) := by
    rw [rlc_pimsEdgeEquiv_reflected_mk_of_adj hfgAdj.1] at hmap
    calc
      sharedPrimalEdge f g =
          rlc_pimsEdgeEquiv
            s((![-1, s + 1] : Site 2), ![0, s + 1]) := hmap
      _ = s((![0, s] : Site 2), ![0, s + 1]) := by
        simpa using (rlc_pimsEdgeEquiv_horizontal (-1) (s + 1))
  exact L.no_lower_contour_axis_crossing hfg hshared hsLower hs


theorem rlc_faceBoundaryWalk_reflected_axis_crossing
    {H : Set (Site 2)} {a b : Site 2}
    (p : (faceBoundaryGraph H).Walk a b)
    (ha : (rlc_dualReflect a) 0 < 0)
    (hb : 0 ≤ (rlc_dualReflect b) 0) :
    ∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ p.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) := by
  let q : (hypercubicLattice 2).Walk a b :=
    p.mapLe (faceBoundaryGraph_le H)
  let S : Set (Site 2) := {z | (rlc_dualReflect z) 0 < 0}
  obtain ⟨f, g, hfgBoundary, hfgEdge⟩ :=
    rlc_walk_mem_edgeBoundary_edges S q (by simpa [S] using ha)
      (by simpa [S] using hb)
  have hfgAdj : (hypercubicLattice 2).Adj
      (rlc_dualReflect f) (rlc_dualReflect g) :=
    (rlc_adj_dualReflect f g).mp hfgBoundary.1
  have hsign :
      ((rlc_dualReflect f) 0 < 0 ↔
        ¬ (rlc_dualReflect g) 0 < 0) := by
    simpa [S] using hfgBoundary.2
  have hsignCases :
      (((rlc_dualReflect f) 0 < 0 ∧
          0 ≤ (rlc_dualReflect g) 0) ∨
        ((rlc_dualReflect g) 0 < 0 ∧
          0 ≤ (rlc_dualReflect f) 0)) := by
    by_cases hf : (rlc_dualReflect f) 0 < 0
    · left
      exact ⟨hf, by
        have hg := hsign.mp hf
        omega⟩
    · right
      have hg : (rlc_dualReflect g) 0 < 0 := by
        by_contra hg
        exact hf (hsign.mpr hg)
      exact ⟨hg, by omega⟩
  have hcross : ∃ k : Int,
      s(rlc_dualReflect f, rlc_dualReflect g) =
        s((![-1, k] : Site 2), ![0, k]) := by
    rcases hsignCases with hfg | hgf
    · rcases adj_cases hfgAdj with ⟨h0, h1⟩ | ⟨h1, h0⟩
      · exfalso
        omega
      · rcases h0 with h0 | h0
        all_goals
          refine ⟨(rlc_dualReflect f) 1, ?_⟩
          have hf0 : (rlc_dualReflect f) 0 = -1 := by omega
          have hg0 : (rlc_dualReflect g) 0 = 0 := by omega
          have hfg1 : (rlc_dualReflect g) 1 =
              (rlc_dualReflect f) 1 := by omega
          have hf : rlc_dualReflect f =
              (![-1, (rlc_dualReflect f) 1] : Site 2) := by
            ext i
            fin_cases i
            · simpa using hf0
            · simp
          have hg : rlc_dualReflect g =
              (![0, (rlc_dualReflect f) 1] : Site 2) := by
            ext i
            fin_cases i
            · simpa using hg0
            · simpa using hfg1
          simp [hf, hg]
    · rcases adj_cases hfgAdj with ⟨h0, h1⟩ | ⟨h1, h0⟩
      · exfalso
        omega
      · rcases h0 with h0 | h0
        all_goals
          refine ⟨(rlc_dualReflect f) 1, ?_⟩
          have hf0 : (rlc_dualReflect f) 0 = 0 := by omega
          have hg0 : (rlc_dualReflect g) 0 = -1 := by omega
          have hfg1 : (rlc_dualReflect g) 1 =
              (rlc_dualReflect f) 1 := by omega
          have hf : rlc_dualReflect f =
              (![0, (rlc_dualReflect f) 1] : Site 2) := by
            ext i
            fin_cases i
            · simpa using hf0
            · simp
          have hg : rlc_dualReflect g =
              (![-1, (rlc_dualReflect f) 1] : Site 2) := by
            ext i
            fin_cases i
            · simpa using hg0
            · simpa using hfg1
          simp [hf, hg, Sym2.eq_swap]
  obtain ⟨k, hk⟩ := hcross
  refine ⟨f, g, k, ?_, hk⟩
  simpa [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using hfgEdge


theorem rlc_faceBoundaryWalk_first_reflected_axis_crossing
    {H : Set (Site 2)} {a b : Site 2}
    (p : (faceBoundaryGraph H).Walk a b)
    (ha : (rlc_dualReflect a) 0 < 0)
    (hb : 0 ≤ (rlc_dualReflect b) 0) :
    ∃ (u v : Site 2) (k : Int)
      (q : (faceBoundaryGraph H).Walk a u),
      (faceBoundaryGraph H).Adj u v ∧
        s(u, v) ∈ p.edges ∧
        (∀ e ∈ q.edges, e ∈ p.edges) ∧
        (∀ z ∈ q.support, (rlc_dualReflect z) 0 < 0) ∧
        s(rlc_dualReflect u, rlc_dualReflect v) =
          s((![-1, k] : Site 2), ![0, k]) := by
  let P : Site 2 → Prop := fun z => (rlc_dualReflect z) 0 < 0
  obtain ⟨u, v, q, huv, huvEdge, hqEdges, hqSafe, hv⟩ :=
    rlc_walk_pred_first_exit_prefix p P ha (by
      dsimp only [P]
      omega)
  let one : (faceBoundaryGraph H).Walk u v := .cons huv .nil
  obtain ⟨f, g, k, hfg, hreflected⟩ :=
    rlc_faceBoundaryWalk_reflected_axis_crossing one
      (hqSafe u q.end_mem_support) (by
        dsimp only [P] at hv
        omega)
  have heq : s(f, g) = s(u, v) := by
    simpa [one] using hfg
  refine ⟨u, v, k, q, huv, huvEdge, hqEdges, hqSafe, ?_⟩
  calc
    s(rlc_dualReflect u, rlc_dualReflect v) =
        s(rlc_dualReflect f, rlc_dualReflect g) := by
      simpa [Sym2.map_mk] using
        congrArg (Sym2.map rlc_dualReflect) heq.symm
    _ = s((![-1, k] : Site 2), ![0, k]) := hreflected


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_band_axis_crossing_walk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a b : Site 2}
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk a b)
    (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
    (ha : (rlc_dualReflect a) 0 < 0)
    (hb : 0 ≤ (rlc_dualReflect b) 0)
    (hpBand : ∀ z ∈ p.support,
      (gamma.1.1 : Site 2) 1 < (rlc_dualReflect z) 1 ∧
        (rlc_dualReflect z) 1 ≤ L.boundary.height) : False := by
  obtain ⟨f, g, k, hfg, hreflected⟩ :=
    rlc_faceBoundaryWalk_reflected_axis_crossing p ha hb
  have hfHeight : (rlc_dualReflect f) 1 = k := by
    have hfMem : rlc_dualReflect f ∈
        s((![-1, k] : Site 2), ![0, k]) := by
      rw [← hreflected]
      exact Sym2.mem_mk_left _ _
    rw [Sym2.mem_iff] at hfMem
    rcases hfMem with hfMem | hfMem
    · have h := congrArg (fun z : Site 2 => z 1) hfMem
      simpa only [Matrix.cons_val_one] using h
    · have h := congrArg (fun z : Site 2 => z 1) hfMem
      simpa only [Matrix.cons_val_one] using h
  have hfBand := hpBand f (p.fst_mem_support_of_mem_edges hfg)
  have hcontour : s(f, g) ∈ L.boundary.contour.edges := hpEdges _ hfg
  apply L.no_lower_reflected_axis_crossing hcontour
      (s := k - 1) (by simpa using hreflected)
  · omega
  · omega


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.lower_band_walk_same_halfplane
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a b : Site 2}
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk a b)
    (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
    (hpBand : ∀ z ∈ p.support,
      (gamma.1.1 : Site 2) 1 < (rlc_dualReflect z) 1 ∧
        (rlc_dualReflect z) 1 ≤ L.boundary.height) :
    ((rlc_dualReflect a) 0 < 0 ↔
      (rlc_dualReflect b) 0 < 0) := by
  constructor
  · intro ha
    by_contra hb
    exact L.no_lower_band_axis_crossing_walk p hpEdges ha (by omega) hpBand
  · intro hb
    by_contra ha
    apply L.no_lower_band_axis_crossing_walk p.reverse
    · intro e he
      apply hpEdges e
      simpa using he
    · simpa using hb
    · omega
    · intro z hz
      apply hpBand z
      simpa [SimpleGraph.Walk.support_reverse] using hz


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.no_lower_band_strict_contact_arc
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {x y : Site 2}
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk y x)
    (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hxNe : rlc_dualReflect x ≠ (gamma.1.1 : Site 2))
    (hyNe : rlc_dualReflect y ≠ (gamma'.1.2.1 : Site 2))
    (hpBand : ∀ z ∈ p.support,
      (gamma.1.1 : Site 2) 1 < (rlc_dualReflect z) 1 ∧
        (rlc_dualReflect z) 1 ≤ L.boundary.height) : False := by
  have hyNeg := hfaith.left_vertex_strict hyPath hyNe
  have hxPos := hfaith.right_vertex_strict hxPath hxNe
  have hsame := L.lower_band_walk_same_halfplane p hpEdges hpBand
  have hxNotNeg : ¬ (rlc_dualReflect x) 0 < 0 := by omega
  exact hxNotNeg (hsame.mp hyNeg)


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_axis_arc
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ a : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          L.boundary.firstFace L.boundary.secondFace,
      s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧
        ∀ e ∈ a.edges, e ∈ L.boundary.contour.edges := by
  classical
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  let G := faceBoundaryGraph H
  obtain ⟨T, hT⟩ := exists_finset_support_faceBoundaryGraph H
    (rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho)
  obtain ⟨u, c, hcyc, hedge⟩ :=
    EvenDegree.exists_cycle_through_edge_of_even_of_finite_support
      G T hT (degree_faceBoundaryGraph_even H) L.boundary.anchor_adj
  have hreach : (G.deleteEdges
      {s(L.boundary.firstFace, L.boundary.secondFace)}).Reachable
        L.boundary.firstFace L.boundary.secondFace :=
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
      (G := G)).mpr ⟨u, c, hcyc, hedge⟩ |>.2
  obtain ⟨a, ha⟩ :=
    (SimpleGraph.reachable_deleteEdges_iff_exists_walk (G := G)).mp hreach
  refine ⟨a, ha, ?_⟩
  intro e he
  apply L.boundary.contour_covers e
  exact a.edges_subset_edgeSet he


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_axis_path_exact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ a : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          L.boundary.firstFace L.boundary.secondFace,
      a.IsPath ∧
        s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧
        ∀ e : Sym2 (Site 2),
          e ∈ L.boundary.contour.edges ↔
            e = s(L.boundary.firstFace, L.boundary.secondFace) ∨
              e ∈ a.edges := by
  obtain ⟨a, haPath, haAvoid, haCover⟩ :=
    L.boundary.exactComplementaryAnchorPath
  refine ⟨a.reverse, (SimpleGraph.Walk.isPath_reverse_iff _).2 haPath,
    ?_, ?_⟩
  · simpa [SimpleGraph.Walk.edges_reverse] using haAvoid
  · intro e
    simpa [SimpleGraph.Walk.edges_reverse] using haCover e


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.middlePath_axis_crossing_extreme
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk u v)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hvPos : 0 < (rlc_dualReflect v) 0)
    (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
    (hpAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ p.edges) :
    ∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ p.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k) := by
  obtain ⟨f, g, k, hfg, hreflected⟩ :=
    rlc_faceBoundaryWalk_reflected_axis_crossing p
      huNeg (by omega)
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, L.boundary.height] : Site 2)
        ![0, L.boundary.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, L.boundary.height] : Site 2)
          ![0, L.boundary.height] =
        s((![0, L.boundary.height] : Site 2),
          ![0, L.boundary.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(L.boundary.firstFace, L.boundary.secondFace) =
      s((![-1, L.boundary.height] : Site 2),
        ![0, L.boundary.height]) :=
    sharedPrimalEdge_uncrossInj L.boundary.anchor_adj.1 hcanonicalAdj
      (L.boundary.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect L.boundary.firstFace,
          rlc_dualReflect L.boundary.secondFace) =
        s((![-1, L.boundary.height + 1] : Site 2),
          ![0, L.boundary.height + 1]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [Sym2.map_mk, rlc_dualReflect, rlc_dualReflectFun,
      Sym2.eq_swap] using hmap
  have hkNe : k ≠ L.boundary.height + 1 := by
    intro hk
    subst k
    have hmapped : Sym2.map rlc_dualReflect s(f, g) =
        Sym2.map rlc_dualReflect
          s(L.boundary.firstFace, L.boundary.secondFace) := by
      simpa [Sym2.map_mk] using hreflected.trans htarget.symm
    have heq := Sym2.map.injective rlc_dualReflect.injective hmapped
    exact hpAvoid (heq ▸ hfg)
  refine ⟨f, g, k, hfg, hreflected, ?_⟩
  by_cases hkLower : k ≤ (gamma.1.1 : Site 2) 1
  · exact Or.inl hkLower
  by_cases hkUpper : L.boundary.height + 1 < k
  · exact Or.inr hkUpper
  exfalso
  apply L.no_lower_reflected_axis_crossing (hpEdges _ hfg)
      (s := k - 1) (by simpa using hreflected)
  · omega
  · omega


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.middlePath_exits_lower_anchor_band
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk u v)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hvPos : 0 < (rlc_dualReflect v) 0)
    (hpEdges : ∀ e ∈ p.edges, e ∈ L.boundary.contour.edges)
    (hpAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ p.edges) :
    ∃ z ∈ p.support,
      (rlc_dualReflect z) 1 ≤ (gamma.1.1 : Site 2) 1 ∨
        L.boundary.height < (rlc_dualReflect z) 1 := by
  obtain ⟨f, g, k, hfg, hreflected, hkLow | hkHigh⟩ :=
    L.middlePath_axis_crossing_extreme p huNeg hvPos hpEdges hpAvoid
  all_goals
    have hfMem : rlc_dualReflect f ∈
        s((![-1, k] : Site 2), ![0, k]) := by
      rw [← hreflected]
      exact Sym2.mem_mk_left _ _
    rw [Sym2.mem_iff] at hfMem
    have hfHeight : (rlc_dualReflect f) 1 = k := by
      rcases hfMem with hfMem | hfMem
      all_goals
        have h := congrArg (fun z : Site 2 => z 1) hfMem
        simpa only [Matrix.cons_val_one] using h
    refine ⟨f, p.fst_mem_support_of_mem_edges hfg, ?_⟩
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_axis_crossing_extreme
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ (a : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          L.boundary.firstFace L.boundary.secondFace)
      (f g : Site 2) (k : Int),
      s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧
        (∀ e ∈ a.edges, e ∈ L.boundary.contour.edges) ∧
        s(f, g) ∈ a.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k) := by
  obtain ⟨a, haAvoid, haEdges⟩ := L.complementary_axis_arc
  let anchorHeight := L.boundary.height + 1
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, L.boundary.height] : Site 2)
        ![0, L.boundary.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, L.boundary.height] : Site 2)
          ![0, L.boundary.height] =
        s((![0, L.boundary.height] : Site 2),
          ![0, L.boundary.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(L.boundary.firstFace, L.boundary.secondFace) =
      s((![-1, L.boundary.height] : Site 2),
        ![0, L.boundary.height]) := by
    exact sharedPrimalEdge_uncrossInj L.boundary.anchor_adj.1
      hcanonicalAdj
      (L.boundary.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect L.boundary.firstFace,
          rlc_dualReflect L.boundary.secondFace) =
        s((![-1, anchorHeight] : Site 2), ![0, anchorHeight]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [anchorHeight, Sym2.map_mk, rlc_dualReflect,
      rlc_dualReflectFun, Sym2.eq_swap] using hmap
  have extract {r s : Site 2}
      (p : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk r s)
      (hpEdge : ∀ e ∈ p.edges, e ∈ a.edges)
      (hpStart : (rlc_dualReflect r) 0 < 0)
      (hpEnd : 0 ≤ (rlc_dualReflect s) 0) :
      ∃ (f g : Site 2) (k : Int),
        s(f, g) ∈ a.edges ∧
          s(rlc_dualReflect f, rlc_dualReflect g) =
            s((![-1, k] : Site 2), ![0, k]) ∧
          (k ≤ (gamma.1.1 : Site 2) 1 ∨
            L.boundary.height + 1 < k) := by
    obtain ⟨f, g, k, hfg, hreflected⟩ :=
      rlc_faceBoundaryWalk_reflected_axis_crossing p hpStart hpEnd
    have hfgA : s(f, g) ∈ a.edges := hpEdge _ hfg
    have hkNe : k ≠ anchorHeight := by
      intro hk
      subst k
      have hmapped :
          Sym2.map rlc_dualReflect s(f, g) =
            Sym2.map rlc_dualReflect
              s(L.boundary.firstFace, L.boundary.secondFace) := by
        simpa [Sym2.map_mk] using hreflected.trans htarget.symm
      have heq := Sym2.map.injective rlc_dualReflect.injective hmapped
      exact haAvoid (heq ▸ hfgA)
    have hcontour : s(f, g) ∈ L.boundary.contour.edges :=
      haEdges _ hfgA
    have hextreme : k ≤ (gamma.1.1 : Site 2) 1 ∨
        L.boundary.height + 1 < k := by
      by_cases hkLower : k ≤ (gamma.1.1 : Site 2) 1
      · exact Or.inl hkLower
      by_cases hkUpper : L.boundary.height + 1 < k
      · exact Or.inr hkUpper
      exfalso
      apply L.no_lower_reflected_axis_crossing hcontour
          (s := k - 1) (by simpa using hreflected)
      · omega
      · dsimp only [anchorHeight] at hkNe
        omega
    exact ⟨f, g, k, hfgA, hreflected, hextreme⟩
  have htargetCases := htarget
  rw [Sym2.eq_iff] at htargetCases
  rcases htargetCases with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · have hstart : (rlc_dualReflect L.boundary.firstFace) 0 < 0 := by
      have h := congrArg (fun z : Site 2 => z 0) hfirst
      simp [rlc_dualReflect, rlc_dualReflectFun] at h ⊢
      omega
    have hend : 0 ≤ (rlc_dualReflect L.boundary.secondFace) 0 := by
      have h := congrArg (fun z : Site 2 => z 0) hsecond
      simp [rlc_dualReflect, rlc_dualReflectFun] at h ⊢
      omega
    obtain ⟨f, g, k, hfg, hreflected, hextreme⟩ :=
      extract a (fun _ he => he) hstart hend
    exact ⟨a, f, g, k, haAvoid, haEdges, hfg, hreflected, hextreme⟩
  · have hstart :
        (rlc_dualReflect L.boundary.secondFace) 0 < 0 := by
      have h := congrArg (fun z : Site 2 => z 0) hsecond
      simp [rlc_dualReflect, rlc_dualReflectFun] at h ⊢
      omega
    have hend : 0 ≤ (rlc_dualReflect L.boundary.firstFace) 0 := by
      have h := congrArg (fun z : Site 2 => z 0) hfirst
      simp [rlc_dualReflect, rlc_dualReflectFun] at h ⊢
      omega
    obtain ⟨f, g, k, hfg, hreflected, hextreme⟩ :=
      extract a.reverse (by intro e he; simpa using he) hstart hend
    exact ⟨a, f, g, k, haAvoid, haEdges, hfg, hreflected, hextreme⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.complementary_first_axis_crossing_extreme
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ (a : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          L.boundary.firstFace L.boundary.secondFace)
      (N u v : Site 2) (k : Int)
      (q : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk N u),
      (N = L.boundary.firstFace ∨ N = L.boundary.secondFace) ∧
        rlc_dualReflect N =
          (![-1, L.boundary.height + 1] : Site 2) ∧
        s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧
        a.IsPath ∧
        (∀ e : Sym2 (Site 2),
          e ∈ L.boundary.contour.edges ↔
            e = s(L.boundary.firstFace, L.boundary.secondFace) ∨
              e ∈ a.edges) ∧
        (∀ e ∈ a.edges, e ∈ L.boundary.contour.edges) ∧
        (∀ e ∈ q.edges, e ∈ a.edges) ∧
        (∀ z ∈ q.support, (rlc_dualReflect z) 0 < 0) ∧
        (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
        s(u, v) ∈ a.edges ∧
        s(rlc_dualReflect u, rlc_dualReflect v) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k) := by
  obtain ⟨a, haPath, haAvoid, haExact⟩ :=
    L.complementary_axis_path_exact
  have haEdges : ∀ e ∈ a.edges, e ∈ L.boundary.contour.edges := by
    intro e he
    exact (haExact e).2 (Or.inr he)
  let anchorHeight := L.boundary.height + 1
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, L.boundary.height] : Site 2)
        ![0, L.boundary.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, L.boundary.height] : Site 2)
          ![0, L.boundary.height] =
        s((![0, L.boundary.height] : Site 2),
          ![0, L.boundary.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(L.boundary.firstFace, L.boundary.secondFace) =
      s((![-1, L.boundary.height] : Site 2),
        ![0, L.boundary.height]) :=
    sharedPrimalEdge_uncrossInj L.boundary.anchor_adj.1 hcanonicalAdj
      (L.boundary.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect L.boundary.firstFace,
          rlc_dualReflect L.boundary.secondFace) =
        s((![-1, anchorHeight] : Site 2), ![0, anchorHeight]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [anchorHeight, Sym2.map_mk, rlc_dualReflect,
      rlc_dualReflectFun, Sym2.eq_swap] using hmap
  have extract {r t : Site 2}
      (p : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk r t)
      (hr : r = L.boundary.firstFace ∨ r = L.boundary.secondFace)
      (hrEq : rlc_dualReflect r = (![-1, anchorHeight] : Site 2))
      (htNonneg : 0 ≤ (rlc_dualReflect t) 0)
      (hpEdge : ∀ e ∈ p.edges, e ∈ a.edges) :
      ∃ (u v : Site 2) (k : Int)
        (q : (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk r u),
        (∀ e ∈ q.edges, e ∈ a.edges) ∧
          (∀ z ∈ q.support, (rlc_dualReflect z) 0 < 0) ∧
          (faceBoundaryGraph
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
          s(u, v) ∈ a.edges ∧
          s(rlc_dualReflect u, rlc_dualReflect v) =
            s((![-1, k] : Site 2), ![0, k]) ∧
          (k ≤ (gamma.1.1 : Site 2) 1 ∨
            L.boundary.height + 1 < k) := by
    obtain ⟨u, v, k, q, huv, huvP, hqP, hqSafe, hreflected⟩ :=
      rlc_faceBoundaryWalk_first_reflected_axis_crossing p
        (by rw [hrEq]; simp) htNonneg
    have huvA := hpEdge _ huvP
    have hqA : ∀ e ∈ q.edges, e ∈ a.edges := by
      intro e he
      exact hpEdge e (hqP e he)
    have hkNe : k ≠ anchorHeight := by
      intro hk
      subst k
      have hmapped : Sym2.map rlc_dualReflect s(u, v) =
          Sym2.map rlc_dualReflect
            s(L.boundary.firstFace, L.boundary.secondFace) := by
        simpa [Sym2.map_mk] using hreflected.trans htarget.symm
      have heq := Sym2.map.injective rlc_dualReflect.injective hmapped
      exact haAvoid (heq ▸ huvA)
    have hcontour := haEdges _ huvA
    have hextreme : k ≤ (gamma.1.1 : Site 2) 1 ∨
        L.boundary.height + 1 < k := by
      by_cases hkLower : k ≤ (gamma.1.1 : Site 2) 1
      · exact Or.inl hkLower
      by_cases hkUpper : L.boundary.height + 1 < k
      · exact Or.inr hkUpper
      exfalso
      apply L.no_lower_reflected_axis_crossing hcontour
          (s := k - 1) (by simpa using hreflected)
      · omega
      · dsimp only [anchorHeight] at hkNe
        omega
    exact ⟨u, v, k, q, hqA, hqSafe, huv, huvA,
      hreflected, hextreme⟩
  have hcases := htarget
  rw [Sym2.eq_iff] at hcases
  rcases hcases with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · have hend : 0 ≤ (rlc_dualReflect L.boundary.secondFace) 0 := by
      have h := congrArg (fun z : Site 2 => z 0) hsecond
      simp [rlc_dualReflect, rlc_dualReflectFun] at h ⊢
      omega
    obtain ⟨u, v, k, q, hqA, hqSafe, huv, huvA, href, hextreme⟩ :=
      extract a (Or.inl rfl) hfirst hend (fun _ he => he)
    exact ⟨a, L.boundary.firstFace, u, v, k, q, Or.inl rfl,
      hfirst, haAvoid, haPath, haExact, haEdges, hqA, hqSafe, huv, huvA,
      href, hextreme⟩
  · have hend : 0 ≤ (rlc_dualReflect L.boundary.firstFace) 0 := by
      have h := congrArg (fun z : Site 2 => z 0) hfirst
      simp [rlc_dualReflect, rlc_dualReflectFun] at h ⊢
      omega
    obtain ⟨u, v, k, q, hqA, hqSafe, huv, huvA, href, hextreme⟩ :=
      extract a.reverse (Or.inr rfl) hsecond hend
        (by intro e he; simpa using he)
    exact ⟨a, L.boundary.secondFace, u, v, k, q, Or.inr rfl,
      hsecond, haAvoid, haPath, haExact, haEdges, hqA, hqSafe, huv, huvA,
      href, hextreme⟩


theorem RlcCentralFaceRetainedAnchoredBoundary.filledReachSet_eq_leftRegion
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) :
    rlc_connectorCentralFaceFilledReachSet gamma gamma' rho =
      jec_leftRegion (B.contour.mapLe
        (faceBoundaryGraph_le
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))) := by
  apply rlc_leftRegion_eq_of_faceBoundaryTrail
  · exact rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho
  · exact B.contour_isTrail
  · exact B.contour_covers


theorem RlcCentralFaceRetainedAnchoredBoundary.reflectedFilledReachSet_eq_leftRegion
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) :
    rlc_reflectedPrimalRegion
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) =
      jec_leftRegion
        ((B.contour.mapLe
          (faceBoundaryGraph_le
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
              rlc_dualReflectLatticeHom) := by
  exact rlc_reflectedRegion_eq_leftRegion_map_of_eq _ _
    B.filledReachSet_eq_leftRegion


theorem rlc_bdEdge_reflectedPrimalRegion_map (K : Set (Site 2))
    (e : Sym2 (Site 2)) :
    bdEdge (rlc_reflectedPrimalRegion K) (Sym2.map rlc_primalDualReflect e) ↔
      bdEdge K e := by
  induction e using Sym2.inductionOn with
  | _ p q =>
      rw [Sym2.map_mk, bdEdge_mk, bdEdge_mk]
      simp only [rlc_mem_reflectedPrimalRegion_iff,
        Equiv.symm_apply_apply]


end
end StatMech.Universality
