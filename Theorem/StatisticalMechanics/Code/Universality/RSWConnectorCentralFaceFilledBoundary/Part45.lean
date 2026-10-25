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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part41
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem RlcCentralFacePairedTerminalSideChange.positiveIncoming_firstIntersectionCycle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v u' v' : Site 2}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hpaired : RlcCentralFacePairedTerminalSideChange
      gamma gamma' rho L u v u' v') :
    ∃ (t' h' k' : Site 2)
      (c : (hypercubicLattice 2).Walk
        (gamma.1.1 : Site 2) (gamma.1.1 : Site 2)),
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Adj t' u' ∧
      s(rlc_dualReflect t', rlc_dualReflect u') ∈
        rlc_reflectedPathEdges gamma'.1 ∧
      h' ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
      flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧
      c.IsCycle ∧
      (∀ e ∈ c.edges,
        e ∈ rlc_connectorFourTraceEdges gamma gamma') ∧
      phb_doubleDualEquiv.symm h' ∈ jec_leftRegion c ∧
      s(rlc_dualReflect t', rlc_dualReflect u') ∈ c.edges ∧
      phb_doubleDualEquiv.symm k' ∉ jec_leftRegion c := by
  obtain ⟨_t, _h, t', h', _htu, _htuRight, _hhRegion, _hhFlank,
    _huvNonwall, _huBox, _hvBox, _huvNoCentral,
    ht'u', ht'u'Left, hh'Region, hh'Flank,
    _hu'v'Nonwall, _hu'Box, _hv'Box, _hu'v'NoCentral,
    _hhBox, _hh'Box, _hreach, _k, k', _hflank, hflank',
    _hside, _hside'⟩ := hpaired
  obtain ⟨c, hcycle, hedges, hcentral, hleftDichotomy⟩ :=
    rlc_centralRegion_inside_firstIntersectionCycle
      gamma gamma' hfaith
  have hambient : s(rlc_dualReflect t', rlc_dualReflect u') ∈
      ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).edges :=
    rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
      gamma'.1 ht'u'Left
  have hh'Inside := hcentral h' hh'Region
  have hedge : s(rlc_dualReflect t', rlc_dualReflect u') ∈ c.edges := by
    rcases hleftDichotomy hambient with hedge | hexterior
    · exact hedge
    · exact False.elim ((hexterior h' hh'Flank) hh'Inside)
  have hadj : (hypercubicLattice 2).Adj
      (rlc_dualReflect t') (rlc_dualReflect u') :=
    (rlc_adj_dualReflect t' u').mp ht'u'.1.1
  have hk'Outside := rlc_cycleEdge_oppositeFlank_outside
    hcycle hadj hflank' hedge hh'Inside
  exact ⟨t', h', k', c, ht'u', ht'u'Left, hh'Region, hflank',
    hcycle, hedges, hh'Inside, hedge, hk'Outside⟩


theorem RlcCentralFacePairedTerminalSideChange.nonwallGoodContourEdge_or_sameWindingSides
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v u' v' : Site 2}
    (hpaired : RlcCentralFacePairedTerminalSideChange
      gamma gamma' rho L u v u' v') :
    (∃ f g : Site 2,
      s(f, g) ∈ L.boundary.contour.edges ∧
        RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
        s(rlc_dualReflect f, rlc_dualReflect g) ∉
          rlc_connectorFourTraceEdges gamma gamma') ∨
      ∃ t h t' h' k k' : Site 2,
        h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
          h' ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
          flankFaces (rlc_dualReflect t) (rlc_dualReflect u) = s(h, k) ∧
          flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧
          (let C := (L.boundary.contour.mapLe
            (faceBoundaryGraph_le
              (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
                rlc_dualReflectLatticeHom
           (phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ↔
              phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C) ∧
            (phb_doubleDualEquiv.symm k ∈ jec_leftRegion C ↔
              phb_doubleDualEquiv.symm k' ∈ jec_leftRegion C)) := by
  obtain ⟨t, h, t', h', _htu, _htuRight, hhRegion, _hhFlank,
    _huvNonwall, _huBox, _hvBox, _huvNoCentral,
    _ht'u', _ht'u'Left, hh'Region, _hh'Flank,
    _hu'v'Nonwall, _hu'Box, _hv'Box, _hu'v'NoCentral,
    hhBox, hh'Box, hreach, k, k', hflank, hflank', hside, hside'⟩ := hpaired
  let C := (L.boundary.contour.mapLe
    (faceBoundaryGraph_le
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
        rlc_dualReflectLatticeHom
  by_cases hopposite :
      (phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C) ∨
        (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C)
  · left
    exact L.boundary.centralCutPath_nonwallGoodContourEdge_of_oppositeSide
      hhRegion hhBox hh'Box hreach hopposite
  · right
    refine ⟨t, h, t', h', k, k', hhRegion, hh'Region,
      hflank, hflank', ?_⟩
    dsimp only at hside hside' ⊢
    have hsame :
        (phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ↔
          phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C) := by
      constructor
      · intro hh
        by_contra hh'
        exact hopposite (Or.inl ⟨hh, hh'⟩)
      · intro hh'
        by_contra hh
        exact hopposite (Or.inr ⟨hh, hh'⟩)
    refine ⟨hsame, ?_⟩
    rcases hside with hside | hside
    · rcases hside' with hside' | hside'
      · exact ⟨fun hk => (hside.2 hk).elim,
          fun hk' => (hside'.2 hk').elim⟩
      · exact (hside'.1 (hsame.mp hside.1)).elim
    · rcases hside' with hside' | hside'
      · exact (hside.1 (hsame.mpr hside'.1)).elim
      · exact ⟨fun _ => hside'.2, fun _ => hside.2⟩


theorem rlc_pairedStrictWallEntryDecomp_boundary_or_terminalSideChange
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v u' v' : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    {q' : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u'}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q')
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v') :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        ((rlc_dualReflect x) 0 = -2 * n ∨
          (rlc_dualReflect x) 0 = 2 * n ∨
          (rlc_dualReflect x) 1 = -n ∨
          (rlc_dualReflect x) 1 = n)) ∨
      RlcCentralFacePairedTerminalSideChange
        gamma gamma' rho L u v u' v' := by
  rcases rlc_negativeStrictWallEntryDecomp_boundary_or_terminalSideChange
      hfaith hneg huv hbad with hboundary | hnegTerminal
  · exact Or.inl hboundary
  rcases rlc_positiveStrictWallEntryDecomp_boundary_or_terminalSideChange
      hfaith hpos hu'v' hbad' with hboundary | hposTerminal
  · exact Or.inl hboundary
  right
  obtain ⟨t, h, htu, htuRight, hhRegion, hhFlank,
    huvNonwall, huBox, hvBox, huvNoCentral⟩ := hnegTerminal
  obtain ⟨t', h', ht'u', ht'u'Left, hh'Region, hh'Flank,
    hu'v'Nonwall, hu'Box, hv'Box, hu'v'NoCentral⟩ := hposTerminal
  have hpaired :=
    L.boundary.pairedCentralIncomingFlanks_cutReachable_and_sideToggle
      htu.1 hhRegion hhFlank ht'u'.1 hh'Region hh'Flank
  exact ⟨t, h, t', h', htu, htuRight, hhRegion, hhFlank,
    huvNonwall, huBox, hvBox, huvNoCentral, ht'u', ht'u'Left,
    hh'Region, hh'Flank, hu'v'Nonwall, hu'Box, hv'Box,
    hu'v'NoCentral, hpaired⟩


end
end StatMech.Universality
