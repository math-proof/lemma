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
import Structure.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem RlcCentralFaceRetainedAnchoredBoundary.contour_isCycle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) :
    B.contour.IsCycle := by
  apply rlc_isCycle_of_isCycles_isTrail B.contour
    (rlc_connectorCentralFaceFilledBoundary_isCycles gamma gamma' rho)
  · intro hnil
    have hanchor := B.anchor_mem
    rw [hnil] at hanchor
    simpa using hanchor
  · exact B.contour_isTrail


theorem RlcCentralFaceRetainedAnchoredBoundary.exists_orientedAnchorCycle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ c : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          B.firstFace B.firstFace,
      c.IsCycle ∧ c.snd = B.secondFace ∧
        c.toSubgraph.verts = B.contour.toSubgraph.verts := by
  have hanchorSub : B.contour.toSubgraph.Adj
      B.firstFace B.secondFace :=
    B.contour.adj_toSubgraph_iff_mem_edges.mpr B.anchor_mem
  exact B.contour_isCycle.exists_isCycle_snd_verts_eq hanchorSub


theorem RlcCentralFaceRetainedAnchoredBoundary.exactComplementaryAnchorPath
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) :
    ∃ a : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          B.secondFace B.firstFace,
      a.IsPath ∧
        s(B.firstFace, B.secondFace) ∉ a.edges ∧
        ∀ e : Sym2 (Site 2),
          e ∈ B.contour.edges ↔
            e = s(B.firstFace, B.secondFace) ∨ e ∈ a.edges := by
  let G := faceBoundaryGraph
    (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
  obtain ⟨c, hc, hsnd, hverts⟩ := B.exists_orientedAnchorCycle
  let a : G.Walk B.secondFace B.firstFace := c.tail.copy hsnd rfl
  have haPath : a.IsPath := by
    simpa [a] using hc.isPath_tail
  have hdecomp : c.edges =
      s(B.firstFace, B.secondFace) :: a.edges := by
    cases c with
    | nil => exact False.elim (hc.ne_nil rfl)
    | @cons u v w huv p =>
        have hv : v = B.secondFace :=
          (SimpleGraph.Walk.snd_cons p huv).symm.trans hsnd
        simp only [SimpleGraph.Walk.edges_cons, a,
          SimpleGraph.Walk.tail_cons]
        rw [SimpleGraph.Walk.edges_copy]
        congr 1
        · exact congrArg (Sym2.mk B.firstFace) hv
        · exact (SimpleGraph.Walk.edges_copy p _ _).symm
  have hcycles : G.IsCycles :=
    rlc_connectorCentralFaceFilledBoundary_isCycles gamma gamma' rho
  have hsameEdges (e : Sym2 (Site 2)) :
      e ∈ c.edges ↔ e ∈ B.contour.edges := by
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [← c.adj_toSubgraph_iff_mem_edges,
          ← B.contour.adj_toSubgraph_iff_mem_edges]
        constructor
        · intro hxy
          have hxC : x ∈ c.toSubgraph.verts :=
            c.toSubgraph.edge_vert hxy
          have hxB : x ∈ B.contour.toSubgraph.verts := by
            rwa [← hverts]
          exact (B.contour_isCycle.adj_toSubgraph_iff_of_isCycles
            hcycles hxB y).2 hxy.adj_sub
        · intro hxy
          have hxB : x ∈ B.contour.toSubgraph.verts :=
            B.contour.toSubgraph.edge_vert hxy
          have hxC : x ∈ c.toSubgraph.verts := by
            rwa [hverts]
          exact (hc.adj_toSubgraph_iff_of_isCycles
            hcycles hxC y).2 hxy.adj_sub
  have haAvoid : s(B.firstFace, B.secondFace) ∉ a.edges := by
    have hnodup := hc.edges_nodup
    rw [hdecomp, List.nodup_cons] at hnodup
    exact hnodup.1
  refine ⟨a, haPath, haAvoid, ?_⟩
  intro e
  rw [← hsameEdges, hdecomp, List.mem_cons]


theorem rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {z : Site 2} (hzPath : z ∈ rlc_pathVertices gamma'.1) :
    z ∈ rlc_connectorCentralFaceExteriorSet gamma gamma' rho := by
  classical
  let K := rlc_connectorCentralFaceReachSet gamma gamma' rho
  obtain ⟨t, _htLower, _htUpper, _htIn, habove, hqExt⟩ :=
    rlc_centralFace_verticalGap_outside_mem_exterior
      gamma gamma' hposition rho hno
  let upper := (gamma'.1.2.1 : Site 2) 1
  have hupperCoord : (![0, upper] : Site 2) = gamma'.1.2.1 := by
    ext i
    fin_cases i <;> simp [upper, gamma'.1.2.1.2.2]
  let W := rlc_ambientCrossingWalk gamma'.1
  have hzW : z ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 z).2
      hzPath
  let wTrace : (hypercubicLattice 2).Walk z
      (gamma'.1.2.1 : Site 2) := (W.takeUntil z hzW).reverse.append W
  let wAxis : (hypercubicLattice 2).Walk
      (gamma'.1.2.1 : Site 2) ![0, t + 1] :=
    (sw_vertSeg 0 upper (t + 1)).copy hupperCoord rfl
  let w := wTrace.append wAxis
  have hwNot : ∀ v ∈ w.support, v ∈ Kᶜ := by
    intro v hv
    dsimp only [w] at hv
    rw [SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hvTrace | hvAxis
    · have hvW : v ∈ W.support := by
        dsimp only [wTrace] at hvTrace
        rw [SimpleGraph.Walk.mem_support_append_iff,
          SimpleGraph.Walk.support_reverse] at hvTrace
        rcases hvTrace with hvTrace | hvTrace
        · exact W.support_takeUntil_subset_support hzW (by simpa using hvTrace)
        · exact hvTrace
      have hvPath :=
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma'.1 v).1 hvW
      exact rlc_leftPathVertex_not_mem_centralFaceReachSet_of_failure
        gamma gamma' rho hno hvPath
    · change v ∈ ((sw_vertSeg 0 upper (t + 1)).copy _ _).support at hvAxis
      rw [SimpleGraph.Walk.support_copy, sw_vertSeg_mem_support] at hvAxis
      obtain ⟨s, hs, rfl⟩ := hvAxis
      rw [Set.mem_uIcc] at hs
      rcases hs with hs | hs
      · exact habove s (by omega) (by omega)
      · exact habove s (by omega) (by omega)
  have hzNot : z ∈ Kᶜ := hwNot z w.start_mem_support
  have hqNot : (![0, t + 1] : Site 2) ∈ Kᶜ := hqExt.1
  have hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨z, hzNot⟩ ⟨![0, t + 1], hqNot⟩ := ⟨w.induce Kᶜ hwNot⟩
  refine ⟨hzNot, ?_⟩
  exact (ConnectedComponent.sound hreach).trans hqExt.2


theorem rlc_centralFaceLowestFilledAxisGap_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    Nonempty (RlcCentralFaceLowestFilledAxisGap gamma gamma' rho) := by
  classical
  let lower := (gamma.1.1 : Site 2) 1
  let upper := (gamma'.1.2.1 : Site 2) 1
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  have hlowerLt : lower < upper := by
    have hr := hposition.right_axis_strict
    have hl := hposition.left_axis_strict
    dsimp only [lower, upper]
    omega
  have hlowerPath : (![0, lower] : Site 2) ∈
      rlc_pathVertices gamma.1 := by
    have haxis : (gamma.1.1 : Site 2) = ![0, lower] := by
      ext i
      fin_cases i <;> simp [lower, gamma.1.1.2.2]
    rw [← haxis]
    exact rlc_path_start_mem_vertices gamma.1
  have hupperPath : (![0, upper] : Site 2) ∈
      rlc_pathVertices gamma'.1 := by
    have haxis : (gamma'.1.2.1 : Site 2) = ![0, upper] := by
      ext i
      fin_cases i <;> simp [upper, gamma'.1.2.1.2.2]
    rw [← haxis]
    exact rlc_connector_path_end_mem_vertices gamma'.1
  have hlower : (![0, lower] : Site 2) ∈ H :=
    rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho
      (rlc_rightPathVertex_mem_centralFaceReachSet
        gamma gamma' rho hlowerPath)
  have hupperExt :=
    rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
      gamma gamma' hposition rho hno hupperPath
  have hupper : (![0, upper] : Site 2) ∉ H := by
    simpa [H, rlc_connectorCentralFaceFilledReachSet] using hupperExt
  let A : Finset Int := (Finset.Icc lower upper).filter
    (fun s => ![0, s] ∉ H)
  have hupperA : upper ∈ A := by
    simp [A, hupper, le_of_lt hlowerLt]
  have hA : A.Nonempty := ⟨upper, hupperA⟩
  let firstOutside := A.min' hA
  have hfirstA : firstOutside ∈ A := A.min'_mem hA
  have hfirstBounds : lower ≤ firstOutside ∧ firstOutside ≤ upper := by
    simpa [A] using (Finset.mem_filter.mp hfirstA).1
  have hfirstOut : (![0, firstOutside] : Site 2) ∉ H :=
    (Finset.mem_filter.mp hfirstA).2
  have hlowerFirst : lower < firstOutside := by
    apply lt_of_le_of_ne hfirstBounds.1
    intro heq
    exact hfirstOut (heq ▸ hlower)
  let t := firstOutside - 1
  have htLower : lower ≤ t := by
    dsimp only [t]
    omega
  have htUpper : t < upper := by
    dsimp only [t]
    omega
  have hbelow : ∀ s : Int, lower ≤ s → s ≤ t → (![0, s] : Site 2) ∈ H := by
    intro s hls hst
    by_contra hsOut
    have hsA : s ∈ A := by
      simp only [A, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hls, by omega⟩, hsOut⟩
    have hmin := A.min'_le s hsA
    change firstOutside ≤ s at hmin
    dsimp only [t] at hst
    omega
  have htIn : (![0, t] : Site 2) ∈ H := hbelow t htLower (le_refl _)
  have htOut : (![0, t + 1] : Site 2) ∉ H := by
    have hsucc : t + 1 = firstOutside := by
      dsimp only [t]
      omega
    rwa [hsucc]
  have hadj : (hypercubicLattice 2).Adj
      (![0, t] : Site 2) ![0, t + 1] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  exact ⟨{
    height := t
    height_lower := htLower
    height_upper := htUpper
    axis_inside := htIn
    axis_outside := htOut
    axis_below_inside := hbelow
    boundary := ⟨hadj, iff_of_true htIn htOut⟩
  }⟩


theorem RlcCentralFaceLowestFilledAxisGap.axis_successor_inside_of_lt
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestFilledAxisGap gamma gamma' rho)
    {s : Int} (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
    (hs : s < L.height) :
    (![0, s + 1] : Site 2) ∈
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
  exact L.axis_below_inside (s + 1) (by omega) (by omega)


theorem RlcCentralFaceLowestFilledAxisGap.no_lower_axis_boundary
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestFilledAxisGap gamma gamma' rho)
    {s : Int} (hsLower : (gamma.1.1 : Site 2) 1 ≤ s)
    (hs : s < L.height) :
    ((![0, s], ![0, s + 1]) ∉ edgeBoundary 2
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) := by
  intro hboundary
  have hsIn := L.axis_below_inside s hsLower (by omega)
  have hsuccIn := L.axis_successor_inside_of_lt hsLower hs
  exact (hboundary.2.mp hsIn) hsuccIn


theorem rlc_centralFace_retainedAnchoredBoundary_of_failure {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hposition : RlcBookPositionedTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    Nonempty (RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho) := by
  classical
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  let hH := rlc_connectorCentralFaceFilledReachSet_finite gamma gamma' rho
  let T := phb_boundarySupport H hH
  obtain ⟨t, htLower, htUpper, htIn, htOut, htBoundary⟩ :=
    rlc_centralFaceFilled_verticalGap_boundary_of_failure
      gamma gamma' hposition rho hno
  obtain ⟨f, g, hfgLat, hshared⟩ := jfc_flankingFaces htBoundary.1
  have hfg : (faceBoundaryGraph H).Adj f g := by
    refine ⟨hfgLat, ?_⟩
    rw [hshared, bdEdge_mk]
    exact htBoundary.2
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
  exact ⟨{
    height := t
    firstFace := f
    secondFace := g
    contour := c
    height_lower := htLower
    height_upper := htUpper
    axis_inside := htIn
    axis_outside := htOut
    anchor_adj := hfg
    anchor_shared := hshared
    contour_isTrail := hcTrail
    contour_covers := hcCovers
    anchor_mem := hanchor
  }⟩


end
end StatMech.Universality
