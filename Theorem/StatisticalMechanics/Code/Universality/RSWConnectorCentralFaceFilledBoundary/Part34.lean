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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part30
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoSignedBadExits_PIMS_or_surgeryResidue
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u' v')
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
        rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨
      RlcCentralFacePairedBadExitSurgeryResidue gamma gamma' rho L u u' := by
  have hu'Reach :=
    (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable.trans q'.reachable
  have finishPositive :
      (∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable L.boundary.firstFace y ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) →
      (rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
          rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨
        RlcCentralFacePairedBadExitSurgeryResidue
          gamma gamma' rho L u u') := by
    intro hleft
    rcases L.positiveBadExit_reachable_right_or_boundary_or_reflectedLeftWall
        hfaith hno hu'Reach hu'Pos hu'v' hbad' with
      hright | hboundary | hwall
    · left
      obtain ⟨y, hyReach, hyPath⟩ := hleft
      obtain ⟨x, hxReach, hxPath⟩ := hright
      apply rlc_centralFacePIMS_success_of_goodComponentContacts
        gamma gamma' rho
      exact ⟨x, y, hxReach.symm.trans hyReach, hxPath, hyPath⟩
    · right
      exact Or.inr (Or.inr (Or.inl hboundary))
    · rcases L.positiveBadExitResidue_boundary_or_axisWallRun_or_lastWallRun
          hfaith q' hu'Pos hu'v' hbad' (Or.inr hwall) with
        hboundary | haxisRun | hlastRun
      · exact Or.inr (Or.inr (Or.inr (Or.inl hboundary)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl haxisRun))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hlastRun))))
  rcases L.negativeBadExit_reachable_left_or_boundary_or_reflectedRightWall
      hfaith hno q.reachable huNeg huv hbad with
    hleft | hboundary | hwall
  · exact finishPositive hleft
  · exact Or.inr (Or.inl hboundary)
  · rcases L.negativeBadExitResidue_left_boundary_or_wallRun
        hfaith q huNeg huv hbad (Or.inr hwall) with
      hleft | hboundary | hlastRun
    · exact finishPositive hleft
    · exact Or.inr (Or.inl hboundary)
    · exact Or.inr (Or.inr (Or.inl hlastRun))


theorem rlc_negativeWallRun_lastEdge_reflectedRight
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hrun : RlcCentralFaceNegativeWallRunSurgeryAt
      gamma gamma' rho L u)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huNotLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1) :
    ∃ t : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma.1 := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAstart, hentry,
    hrWall, hrNotNil, w, hw, huw⟩ := hrun
  let t := r.penultimate
  have htu := r.adj_penultimate hrNotNil
  have htuEdge := r.mk_penultimate_end_mem_edges hrNotNil
  have hwall := hrWall _ htuEdge
  have hwall' : s(rlc_dualReflect t, rlc_dualReflect u) ∈
      rlc_connectorFourTraceEdges gamma gamma' := by
    simpa [t, Sym2.map_mk] using hwall
  have huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1 := by
    intro hu
    have huRect := rlc_pathVertex_mem_rect gamma.1 hu
    rw [mem_rect] at huRect
    omega
  have huNotFlipLeft : ¬ ∃ z ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect u = rlc_flipX z := by
    rintro ⟨z, hz, huz⟩
    have hzRect := rlc_pathVertex_mem_rect gamma'.1 hz
    rw [mem_rect] at hzRect
    have h0 := congrArg (fun x : Site 2 => x 0) huz
    change (rlc_dualReflect u) 0 = -z 0 at h0
    omega
  refine ⟨t, htu, ?_⟩
  exact rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
    gamma gamma' hwall' (Sym2.mem_mk_right _ _)
      huNotRight huNotLeft huNotFlipLeft


theorem rlc_positiveWallRun_lastEdge_reflectedLeft
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hrun : RlcCentralFacePositiveWallRunSurgeryAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1) :
    ∃ t : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma'.1 := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAstart, hentry,
    hrWall, hrNotNil, w, hw, huw⟩ := hrun
  let t := r.penultimate
  have htu := r.adj_penultimate hrNotNil
  have htuEdge := r.mk_penultimate_end_mem_edges hrNotNil
  have hwall := hrWall _ htuEdge
  have hwall' : s(rlc_dualReflect t, rlc_dualReflect u) ∈
      rlc_connectorFourTraceEdges gamma gamma' := by
    simpa [t, Sym2.map_mk] using hwall
  have huNotLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1 := by
    intro hu
    have huRect := rlc_pathVertex_mem_rect gamma'.1 hu
    rw [mem_rect] at huRect
    omega
  have huNotFlipRight : ¬ ∃ z ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect u = rlc_flipX z := by
    rintro ⟨z, hz, huz⟩
    have hzRect := rlc_pathVertex_mem_rect gamma.1 hz
    rw [mem_rect] at hzRect
    have h0 := congrArg (fun x : Site 2 => x 0) huz
    change (rlc_dualReflect u) 0 = -z 0 at h0
    omega
  refine ⟨t, htu, ?_⟩
  exact rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
    gamma gamma' hwall' (Sym2.mem_mk_right _ _)
      huNotRight huNotLeft huNotFlipRight


theorem rlc_positiveAxisAllWallRun_lastEdge_reflectedLeft
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hrun : RlcCentralFacePositiveAxisAllWallRunAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1) :
    ∃ t : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma'.1 := by
  obtain ⟨A, p, hAzero, hALeft, hpWall, w, hw, huw⟩ := hrun
  have hANeU : A ≠ u := by
    intro hAu
    have hreflect : rlc_dualReflect A = rlc_dualReflect u :=
      congrArg rlc_dualReflect hAu
    have h0 := congrArg (fun z : Site 2 => z 0) hreflect
    rw [hAzero] at h0
    simp only [Matrix.cons_val_zero] at h0
    omega
  have hpNotNil : ¬ p.Nil := p.not_nil_of_ne hANeU
  let t := p.penultimate
  have htu := p.adj_penultimate hpNotNil
  have htuEdge := p.mk_penultimate_end_mem_edges hpNotNil
  have hwall := hpWall _ htuEdge
  have hwall' : s(rlc_dualReflect t, rlc_dualReflect u) ∈
      rlc_connectorFourTraceEdges gamma gamma' := by
    simpa [t, Sym2.map_mk] using hwall
  have huNotLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1 := by
    intro hu
    have huRect := rlc_pathVertex_mem_rect gamma'.1 hu
    rw [mem_rect] at huRect
    omega
  have huNotFlipRight : ¬ ∃ z ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect u = rlc_flipX z := by
    rintro ⟨z, hz, huz⟩
    have hzRect := rlc_pathVertex_mem_rect gamma.1 hz
    rw [mem_rect] at hzRect
    have h0 := congrArg (fun x : Site 2 => x 0) huz
    change (rlc_dualReflect u) 0 = -z 0 at h0
    omega
  refine ⟨t, htu, ?_⟩
  exact rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
    gamma gamma' hwall' (Sym2.mem_mk_right _ _)
      huNotRight huNotLeft huNotFlipRight


theorem rlc_negativeWallRun_lastEdge_traceStep
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hrun : RlcCentralFaceNegativeWallRunSurgeryAt
      gamma gamma' rho L u)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huNotLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1) :
    ∃ (t z w : Site 2),
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
        z ∈ rlc_pathVertices gamma.1 ∧
        w ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect t = rlc_flipX z ∧
        rlc_dualReflect u = rlc_flipX w ∧
        s(z, w) ∈ rlc_pathEdges gamma.1 := by
  obtain ⟨t, htu, he⟩ :=
    rlc_negativeWallRun_lastEdge_reflectedRight
      hrun huNeg huNotLeft
  obtain ⟨z, hz, htz⟩ :=
    rlc_reflectedPathEdge_endpoint_mem_vertices gamma.1 he
      (Sym2.mem_mk_left _ _)
  obtain ⟨w, hw, huw⟩ :=
    rlc_reflectedPathEdge_endpoint_mem_vertices gamma.1 he
      (Sym2.mem_mk_right _ _)
  have he' : s(rlc_flipX z, rlc_flipX w) ∈
      rlc_reflectedPathEdges gamma.1 := by
    simpa [htz, huw] using he
  exact ⟨t, z, w, htu, hz, hw, htz, huw,
    rlc_mem_pathEdges_of_reflected_mk gamma.1 he'⟩

theorem rlc_positiveWallRun_lastEdge_traceStep
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hrun : RlcCentralFacePositiveWallRunSurgeryAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1) :
    ∃ (t z w : Site 2),
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
        z ∈ rlc_pathVertices gamma'.1 ∧
        w ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect t = rlc_flipX z ∧
        rlc_dualReflect u = rlc_flipX w ∧
        s(z, w) ∈ rlc_pathEdges gamma'.1 := by
  obtain ⟨t, htu, he⟩ :=
    rlc_positiveWallRun_lastEdge_reflectedLeft
      hrun huPos huNotRight
  obtain ⟨z, hz, htz⟩ :=
    rlc_reflectedPathEdge_endpoint_mem_vertices gamma'.1 he
      (Sym2.mem_mk_left _ _)
  obtain ⟨w, hw, huw⟩ :=
    rlc_reflectedPathEdge_endpoint_mem_vertices gamma'.1 he
      (Sym2.mem_mk_right _ _)
  have he' : s(rlc_flipX z, rlc_flipX w) ∈
      rlc_reflectedPathEdges gamma'.1 := by
    simpa [htz, huw] using he
  exact ⟨t, z, w, htu, hz, hw, htz, huw,
    rlc_mem_pathEdges_of_reflected_mk gamma'.1 he'⟩

theorem rlc_positiveAxisAllWallRun_lastEdge_traceStep
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hrun : RlcCentralFacePositiveAxisAllWallRunAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huNotRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1) :
    ∃ (t z w : Site 2),
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
        z ∈ rlc_pathVertices gamma'.1 ∧
        w ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect t = rlc_flipX z ∧
        rlc_dualReflect u = rlc_flipX w ∧
        s(z, w) ∈ rlc_pathEdges gamma'.1 := by
  obtain ⟨t, htu, he⟩ :=
    rlc_positiveAxisAllWallRun_lastEdge_reflectedLeft
      hrun huPos huNotRight
  obtain ⟨z, hz, htz⟩ :=
    rlc_reflectedPathEdge_endpoint_mem_vertices gamma'.1 he
      (Sym2.mem_mk_left _ _)
  obtain ⟨w, hw, huw⟩ :=
    rlc_reflectedPathEdge_endpoint_mem_vertices gamma'.1 he
      (Sym2.mem_mk_right _ _)
  have he' : s(rlc_flipX z, rlc_flipX w) ∈
      rlc_reflectedPathEdges gamma'.1 := by
    simpa [htz, huw] using he
  exact ⟨t, z, w, htu, hz, hw, htz, huw,
    rlc_mem_pathEdges_of_reflected_mk gamma'.1 he'⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveAxisAllWallRun_reachableRight_or_nonnegativePath
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFacePositiveAxisAllWallRunAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ∃ (A : Site 2)
        (p : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk A u),
        p.IsPath ∧
          rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
          rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∧
          (∀ e ∈ p.edges,
            Sym2.map rlc_dualReflect e ∈
              rlc_connectorFourTraceEdges gamma gamma') ∧
          (∀ z ∈ p.support,
            rlc_dualReflect z ∉ rlc_pathVertices gamma.1) ∧
          ∀ z ∈ p.support, 0 ≤ (rlc_dualReflect z) 0 := by
  obtain ⟨A, w, hAzero, hALeft, hwWall, zEnd, hzEnd, huEnd⟩ := hrun
  let p : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A u := w.toPath
  have hpPath : p.IsPath := w.toPath.isPath
  have hpEdges : ∀ e ∈ p.edges, e ∈ w.edges := by
    intro e he
    exact w.edges_toPath_subset he
  have hpWall : ∀ e ∈ p.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
    intro e he
    exact hwWall e (hpEdges e he)
  obtain ⟨A0, hfirstA0, _hA0first, hA0zero, _hA0class⟩ :=
    rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
      L.boundary hfaith
  have hA0A : A0 = A := by
    apply rlc_dualReflect.injective
    exact hA0zero.trans hAzero.symm
  have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace A := by
    simpa [hA0A] using hfirstA0
  by_cases hright : ∃ x ∈ p.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1
  · left
    obtain ⟨x, hxP, hxRight⟩ := hright
    exact ⟨x, hfirstA.trans ⟨p.takeUntil x hxP⟩, hxRight⟩
  · right
    push Not at hright
    refine ⟨A, p, hpPath, hAzero, hALeft, hpWall, hright, ?_⟩
    intro y hyP
    by_contra hyNonneg
    have hyNeg : (rlc_dualReflect y) 0 < 0 := by omega
    let tailGood := p.dropUntil y hyP
    let tail := tailGood.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)
    obtain ⟨f, g, k, hfgTail, hreflected⟩ :=
      rlc_faceBoundaryWalk_reflected_axis_crossing tail
        (by simpa [tail, tailGood] using hyNeg) (by
          simpa [tail, tailGood] using (le_of_lt huPos))
    have hfgGood : s(f, g) ∈ tailGood.edges := by
      simpa [tail, SimpleGraph.Walk.edges_mapLe_eq_edges] using hfgTail
    have hfgP : s(f, g) ∈ p.edges :=
      p.edges_dropUntil_subset hyP hfgGood
    have hwallAxis : s((![-1, k] : Site 2), ![0, k]) ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
      rw [← hreflected]
      simpa [Sym2.map_mk] using hpWall _ hfgP
    have hzeroBarrier : (![0, k] : Site 2) ∈
        rlc_connectorBarrier gamma gamma' :=
      rlc_mem_connectorBarrier_of_mem_fourTraceEdge
        gamma gamma' hwallAxis (Sym2.mem_mk_right _ _)
    obtain ⟨c, hcTail, hcEq⟩ : ∃ c : Site 2,
        c ∈ tailGood.support ∧
          rlc_dualReflect c = (![0, k] : Site 2) := by
      rw [Sym2.eq_iff] at hreflected
      rcases hreflected with ⟨hf, hg⟩ | ⟨hf, hg⟩
      · exact ⟨g, tailGood.snd_mem_support_of_mem_edges hfgGood, hg⟩
      · exact ⟨f, tailGood.fst_mem_support_of_mem_edges hfgGood, hf⟩
    rcases (rlc_axis_mem_connectorBarrier_iff gamma gamma' k).1
        hzeroBarrier with hzeroRight | hzeroLeft
    · have hcRight : rlc_dualReflect c ∈
          rlc_pathVertices gamma.1 := by
        rwa [hcEq]
      have hcP : c ∈ p.support :=
        p.support_dropUntil_subset hyP hcTail
      exact hright c hcP hcRight
    · have hAEnd := hfaith.left_axis_unique hALeft (by
          rw [hAzero]
          simp)
      have hcLeft : rlc_dualReflect c ∈
          rlc_pathVertices gamma'.1 := by
        simpa [hcEq] using hzeroLeft
      have hcZero : (rlc_dualReflect c) 0 = 0 := by
        rw [hcEq]
        rfl
      have hcEnd := hfaith.left_axis_unique hcLeft hcZero
      have hAc : A = c := by
        apply rlc_dualReflect.injective
        exact hAEnd.trans hcEnd.symm
      have hyc : y ≠ c := by
        intro hyc
        have hyZero : (rlc_dualReflect y) 0 = 0 := by
          simpa [hyc] using hcZero
        omega
      have hAinPrefix : A ∈ (p.takeUntil y hyP).support :=
        (p.takeUntil y hyP).start_mem_support
      have happPath : ((p.takeUntil y hyP).append
          (p.dropUntil y hyP)).IsPath := by
        rw [p.take_spec hyP]
        exact hpPath
      have hAneC := happPath.ne_of_mem_support_of_append
        hyc.symm hAinPrefix hcTail
      exact hAneC hAc


theorem rlc_nonnegative_wallPath_edge_reflectedLeft
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {A u : Site 2}
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A u)
    (hpWall : ∀ e ∈ p.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma')
    (hpNoRight : ∀ z ∈ p.support,
      rlc_dualReflect z ∉ rlc_pathVertices gamma.1)
    (hpNonneg : ∀ z ∈ p.support, 0 ≤ (rlc_dualReflect z) 0)
    {f g : Site 2} (hfg : s(f, g) ∈ p.edges) :
    s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_reflectedPathEdges gamma'.1 := by
  have hfP := p.fst_mem_support_of_mem_edges hfg
  have hgP := p.snd_mem_support_of_mem_edges hfg
  have hfNonneg := hpNonneg f hfP
  have hgNonneg := hpNonneg g hgP
  have hfgWall : s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_connectorFourTraceEdges gamma gamma' := by
    simpa [Sym2.map_mk] using hpWall _ hfg
  have hfgAdj : (hypercubicLattice 2).Adj
      (rlc_dualReflect f) (rlc_dualReflect g) :=
    (rlc_adj_dualReflect f g).mp (p.adj_of_mem_edges hfg).1.1
  have hsomePos : 0 < (rlc_dualReflect f) 0 ∨
      0 < (rlc_dualReflect g) 0 := by
    by_contra hnot
    push Not at hnot
    have hfZero : (rlc_dualReflect f) 0 = 0 := by omega
    have hgZero : (rlc_dualReflect g) 0 = 0 := by omega
    rcases face_adj_dir hfgAdj with hg | hg | hg | hg
    · have h0 := congrArg (fun z : Site 2 => z 0) hg
      simp only [Matrix.cons_val_zero] at h0
      omega
    · have h0 := congrArg (fun z : Site 2 => z 0) hg
      simp only [Matrix.cons_val_zero] at h0
      omega
    · apply rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
        gamma gamma' hfaith ((rlc_dualReflect g) 1)
      have hg1 := congrArg (fun z : Site 2 => z 1) hg
      simp only [rlc_dualReflect_one, Matrix.cons_val_one] at hg1
      have hedge : s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![0, (rlc_dualReflect g) 1 - 1] : Site 2),
            ![0, (rlc_dualReflect g) 1]) := by
        rw [Sym2.eq_iff]
        left
        constructor <;> ext i <;> fin_cases i <;>
          simp_all
      rwa [← hedge]
    · apply rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
        gamma gamma' hfaith ((rlc_dualReflect f) 1)
      have hg1 := congrArg (fun z : Site 2 => z 1) hg
      simp only [rlc_dualReflect_one, Matrix.cons_val_one] at hg1
      have hedge : s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![0, (rlc_dualReflect f) 1 - 1] : Site 2),
            ![0, (rlc_dualReflect f) 1]) := by
        rw [Sym2.eq_iff]
        right
        constructor <;> ext i <;> fin_cases i <;>
          simp_all
      rwa [← hedge]
  rcases hsomePos with hfPos | hgPos
  · have hfNotLeft : rlc_dualReflect f ∉
        rlc_pathVertices gamma'.1 := by
      intro hfLeft
      have hfRect := rlc_pathVertex_mem_rect gamma'.1 hfLeft
      rw [mem_rect] at hfRect
      omega
    have hfNotFlipRight : ¬ ∃ z ∈ rlc_pathVertices gamma.1,
        rlc_dualReflect f = rlc_flipX z := by
      rintro ⟨z, hz, hfz⟩
      have hzRect := rlc_pathVertex_mem_rect gamma.1 hz
      rw [mem_rect] at hzRect
      have h0 := congrArg (fun x : Site 2 => x 0) hfz
      change (rlc_dualReflect f) 0 = -z 0 at h0
      omega
    exact rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
      gamma gamma' hfgWall (Sym2.mem_mk_left _ _)
        (hpNoRight f hfP) hfNotLeft hfNotFlipRight
  · have hgNotLeft : rlc_dualReflect g ∉
        rlc_pathVertices gamma'.1 := by
      intro hgLeft
      have hgRect := rlc_pathVertex_mem_rect gamma'.1 hgLeft
      rw [mem_rect] at hgRect
      omega
    have hgNotFlipRight : ¬ ∃ z ∈ rlc_pathVertices gamma.1,
        rlc_dualReflect g = rlc_flipX z := by
      rintro ⟨z, hz, hgz⟩
      have hzRect := rlc_pathVertex_mem_rect gamma.1 hz
      rw [mem_rect] at hzRect
      have h0 := congrArg (fun x : Site 2 => x 0) hgz
      change (rlc_dualReflect g) 0 = -z 0 at h0
      omega
    exact rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
      gamma gamma' hfgWall (Sym2.mem_mk_right _ _)
        (hpNoRight g hgP) hgNotLeft hgNotFlipRight


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveAxisAllWallRun_reachableRight_or_reflectedLeftPath
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFacePositiveAxisAllWallRunAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ∃ (A : Site 2)
        (p : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk A u),
        p.IsPath ∧
          rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
          rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∧
          (∀ z ∈ p.support,
            rlc_dualReflect z ∉ rlc_pathVertices gamma.1) ∧
          ∀ {f g : Site 2}, s(f, g) ∈ p.edges →
            s(rlc_dualReflect f, rlc_dualReflect g) ∈
              rlc_reflectedPathEdges gamma'.1 := by
  rcases L.positiveAxisAllWallRun_reachableRight_or_nonnegativePath
      hfaith hrun huPos with hright | hpath
  · exact Or.inl hright
  · right
    obtain ⟨A, p, hpPath, hAzero, hALeft, hpWall,
      hpNoRight, hpNonneg⟩ := hpath
    refine ⟨A, p, hpPath, hAzero, hALeft, hpNoRight, ?_⟩
    intro f g hfg
    exact rlc_nonnegative_wallPath_edge_reflectedLeft
      hfaith p hpWall hpNoRight hpNonneg hfg


theorem rlc_pathSuffix_closed_under_pathEdge
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b z x y : V}
    (W : G.Walk a b) (hW : W.IsPath) (hz : z ∈ W.support)
    (hxSuffix : x ∈ (W.dropUntil z hz).support) (hxNe : x ≠ z)
    (hxy : s(x, y) ∈ W.edges) :
    y ∈ (W.dropUntil z hz).support := by
  classical
  have hsplit : (W.takeUntil z hz).append (W.dropUntil z hz) = W :=
    W.take_spec hz
  have hxySplit : s(x, y) ∈
      ((W.takeUntil z hz).append (W.dropUntil z hz)).edges := by
    rwa [hsplit]
  rw [SimpleGraph.Walk.edges_append, List.mem_append] at hxySplit
  rcases hxySplit with hxyPrefix | hxySuffix
  · have hxPrefix :=
      (W.takeUntil z hz).fst_mem_support_of_mem_edges hxyPrefix
    have hsplitPath :
        ((W.takeUntil z hz).append (W.dropUntil z hz)).IsPath := by
      rwa [hsplit]
    exact False.elim ((hsplitPath.ne_of_mem_support_of_append
      hxNe hxPrefix hxSuffix) rfl)
  · exact (W.dropUntil z hz).snd_mem_support_of_mem_edges hxySuffix


theorem rlc_walk_end_mem_pathSuffix_of_avoid
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b z x y : V}
    (W : G.Walk a b) (hW : W.IsPath) (hz : z ∈ W.support)
    (q : G.Walk x y)
    (hxSuffix : x ∈ (W.dropUntil z hz).support)
    (hqEdges : ∀ e ∈ q.edges, e ∈ W.edges)
    (hqAvoid : z ∉ q.support) :
    y ∈ (W.dropUntil z hz).support := by
  induction q with
  | nil => exact hxSuffix
  | @cons x v y hxv q ih =>
      have hxNe : x ≠ z := by
        intro hxz
        apply hqAvoid
        simp [hxz]
      have hxvEdge : s(x, v) ∈ W.edges := by
        apply hqEdges
        simp
      have hvSuffix := rlc_pathSuffix_closed_under_pathEdge
        W hW hz hxSuffix hxNe hxvEdge
      apply ih hvSuffix
      · intro e he
        apply hqEdges e
        simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
        exact Or.inr he
      · intro hzq
        apply hqAvoid
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
        exact Or.inr hzq


theorem rlc_walk_end_mem_pathSuffix_iff_of_avoid
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b z x y : V}
    (W : G.Walk a b) (hW : W.IsPath) (hz : z ∈ W.support)
    (q : G.Walk x y)
    (hqEdges : ∀ e ∈ q.edges, e ∈ W.edges)
    (hqAvoid : z ∉ q.support) :
    x ∈ (W.dropUntil z hz).support ↔
      y ∈ (W.dropUntil z hz).support := by
  constructor
  · intro hx
    exact rlc_walk_end_mem_pathSuffix_of_avoid
      W hW hz q hx hqEdges hqAvoid
  · intro hy
    apply rlc_walk_end_mem_pathSuffix_of_avoid
      W hW hz q.reverse hy
    · intro e he
      apply hqEdges e
      simpa [SimpleGraph.Walk.edges_reverse] using he
    · intro hzq
      apply hqAvoid
      simpa [SimpleGraph.Walk.support_reverse] using hzq


theorem rlc_walk_all_positive_or_last_nonpositive_decomp
    {V : Type*} {G : SimpleGraph V} (f : V → Int)
    {x y : V} (w : G.Walk x y) (hy : 0 < f y) :
    (∀ z ∈ w.support, 0 < f z) ∨
      ∃ (a b : V) (p : G.Walk x a) (r : G.Walk b y)
        (hab : G.Adj a b),
        f a ≤ 0 ∧
          0 < f b ∧
          (∀ z ∈ r.support, 0 < f z) ∧
          w = p.append (.cons hab r) := by
  induction w with
  | nil =>
      left
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      subst z
      exact hy
  | @cons a b y hab t ih =>
      rcases ih hy with hall | ⟨c, d, p, r, hcd,
        hcNonpos, hdPos, hrPos, hdecomp⟩
      · by_cases haPos : 0 < f a
        · left
          intro z hz
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          exact hz.elim (fun h => h ▸ haPos) (hall z)
        · right
          refine ⟨a, b, .nil, t, hab, by omega, ?_, hall, by simp⟩
          exact hall b t.start_mem_support
      · right
        refine ⟨c, d, .cons hab p, r, hcd,
          hcNonpos, hdPos, hrPos, ?_⟩
        rw [hdecomp]
        rfl


theorem rlc_mem_ambientCrossingWalk_edges_of_mem_pathEdges
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_pathEdges tau) :
    e ∈ (rlc_ambientCrossingWalk tau).edges := by
  let hom : ((hypercubicLattice 2).induce (rect a b c d)) →g
      hypercubicLattice 2 :=
    (SimpleGraph.Embedding.induce (G := hypercubicLattice 2)
      (rect a b c d)).toHom
  let p : ((hypercubicLattice 2).induce (rect a b c d)).Walk _ _ :=
    tau.2.2.1
  change e ∈ (p.map hom).edges
  rw [SimpleGraph.Walk.edges_map, List.mem_map]
  rw [rlc_pathEdges, Finset.mem_image] at he
  obtain ⟨f, hf, hfe⟩ := he
  exact ⟨f, by simpa [p] using hf, by simpa [hom] using hfe⟩


theorem rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_reflectedPathEdges tau) :
    e ∈ ((rlc_ambientCrossingWalk tau).map
      rlc_flipXLatticeHom).edges := by
  rw [rlc_reflectedPathEdges, Finset.mem_image] at he
  obtain ⟨f, hf, hfe⟩ := he
  rw [SimpleGraph.Walk.edges_map, List.mem_map]
  exact ⟨f,
    rlc_mem_ambientCrossingWalk_edges_of_mem_pathEdges tau hf,
    hfe⟩


theorem rlc_reflectedAmbientCrossingWalk_isPath
    {a b c d : Int} (tau : RlcCrossingPath a b c d) :
    ((rlc_ambientCrossingWalk tau).map
      rlc_flipXLatticeHom).IsPath := by
  apply (rlc_ambientCrossingWalk tau).map_isPath_of_injective
  · exact rlc_flipX.injective
  · exact rlc_ambientCrossingWalk_isPath tau


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveAxisAllWallRun_reachableRight_or_firstIntersectionSuffix
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFacePositiveAxisAllWallRunAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      ∃ (z : Site 2)
        (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support)
        (A : Site 2)
        (p : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Walk A u),
        z ∈ rlc_pathVertices gamma.1 ∧
          rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
          p.IsPath ∧
          (∀ x ∈ p.support,
            rlc_dualReflect x ∉ rlc_pathVertices gamma.1) ∧
          rlc_dualReflect u ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support := by
  rcases L.positiveAxisAllWallRun_reachableRight_or_reflectedLeftPath
      hfaith hrun huPos with hright | hpath
  · exact Or.inl hright
  · right
    obtain ⟨A, p, hpPath, hAzero, hALeft,
      hpNoRight, hpReflectedLeft⟩ := hpath
    obtain ⟨z, _hzWR, hzRight, hzLeft, _hfirst, _hglobalMin⟩ :=
      rlc_bookFirstFlippedTraceIntersection_of_faithful
        gamma gamma' hfaith
    let W := (rlc_ambientCrossingWalk gamma'.1).map
      rlc_flipXLatticeHom
    have hflipZWL : rlc_flipX z ∈
        (rlc_ambientCrossingWalk gamma'.1).support :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 (rlc_flipX z)).2 hzLeft
    have hzW : z ∈ W.support := by
      change z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support
      rw [SimpleGraph.Walk.support_map, List.mem_map]
      refine ⟨rlc_flipX z, hflipZWL, ?_⟩
      exact rlc_flipX_involutive z
    let hDual :
        rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho →g
          hypercubicLattice 2 := {
      toFun := rlc_dualReflect
      map_rel' := fun {f g} hfg =>
        (rlc_adj_dualReflect f g).mp hfg.1.1
    }
    let q : (hypercubicLattice 2).Walk
        (rlc_dualReflect A) (rlc_dualReflect u) := p.map hDual
    have hqEdges : ∀ e ∈ q.edges, e ∈ W.edges := by
      intro e he
      change e ∈ (p.map hDual).edges at he
      rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
      obtain ⟨e0, he0, rfl⟩ := he
      induction e0 using Sym2.inductionOn with
      | _ f g =>
          apply rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
            gamma'.1
          exact hpReflectedLeft he0
    have hqAvoid : z ∉ q.support := by
      intro hzq
      change z ∈ (p.map hDual).support at hzq
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
      obtain ⟨x, hxP, hxz⟩ := hzq
      change rlc_dualReflect x = z at hxz
      exact hpNoRight x hxP (by simpa [hxz] using hzRight)
    have hAZero : (rlc_dualReflect A) 0 = 0 := by
      rw [hAzero]
      rfl
    have hAEnd := hfaith.left_axis_unique hALeft hAZero
    have hupperFlip : rlc_flipX (gamma'.1.2.1 : Site 2) =
        (gamma'.1.2.1 : Site 2) :=
      rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
    have hAInSuffix : rlc_dualReflect A ∈
        (W.dropUntil z hzW).support := by
      rw [hAEnd]
      have hend : rlc_flipX (gamma'.1.2.1 : Site 2) ∈
          (W.dropUntil z hzW).support :=
        (W.dropUntil z hzW).end_mem_support
      rw [hupperFlip] at hend
      exact hend
    have huSuffix := rlc_walk_end_mem_pathSuffix_of_avoid
      W (rlc_reflectedAmbientCrossingWalk_isPath gamma'.1)
        hzW q hAInSuffix hqEdges hqAvoid
    exact ⟨z, hzW, A, p, hzRight, hzLeft, hpPath,
      hpNoRight, huSuffix⟩


end
end StatMech.Universality
