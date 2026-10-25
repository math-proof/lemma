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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part37
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem RlcCentralFaceNegativeStrictWallEntryDecompAt.anchoredNonwallGoodContourEdge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    ∃ f g : Site 2,
      s(f, g) ∈ L.boundary.contour.edges ∧
      RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
      s(rlc_dualReflect f, rlc_dualReflect g) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable L.boundary.firstFace f ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable L.boundary.firstFace g := by
  obtain ⟨_A, a, b, pA, p, _r, hab, _hdecomp, _hAzero,
    _hAoff, hentryNot, _hrNeg, _hrNoLeft, _hrRight,
    _hrNotNil⟩ := hentry
  have haReach : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace a :=
    ⟨pA.reverse.append p⟩
  refine ⟨a, b, L.boundary.contour_covers s(a, b) ?_, hab.2,
    hentryNot, haReach, haReach.trans hab.reachable⟩
  rw [SimpleGraph.mem_edgeSet]
  exact hab.1


theorem rlc_goodComponentContacts_or_anchoredNonwallEdgeMissingContactIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
    {f g : Site 2}
    (hfgContour : s(f, g) ∈ B.contour.edges)
    (hcarrier : RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' f g)
    (hnonwall : s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hfirstF : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace f)
    (hfirstG : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace g) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceAnchoredNonwallGoodContourEdgeMissingContactIncidence
        B f g := by
  by_cases hright : ∃ x : Site 2,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable B.firstFace x
  · obtain ⟨x, hxRight, hfirstX⟩ := hright
    by_cases hleft : ∃ y : Site 2,
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable B.firstFace y
    · obtain ⟨y, hyLeft, hfirstY⟩ := hleft
      exact Or.inl ⟨x, y, hfirstX.symm.trans hfirstY, hxRight, hyLeft⟩
    · right
      refine ⟨hfgContour, hcarrier, hnonwall, hfirstF, hfirstG,
        Or.inr ⟨x, hxRight, hfirstX, ?_⟩⟩
      intro y hyLeft hfirstY
      exact hleft ⟨y, hyLeft, hfirstY⟩
  · right
    refine ⟨hfgContour, hcarrier, hnonwall, hfirstF, hfirstG,
      Or.inl ?_⟩
    intro x hxRight hfirstX
    exact hright ⟨x, hxRight, hfirstX⟩


end
end StatMech.Universality
