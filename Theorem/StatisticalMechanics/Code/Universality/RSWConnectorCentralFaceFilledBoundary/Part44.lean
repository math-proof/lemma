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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part40
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_retainedAnchorTraceIncidence_of_strictEntryOriginalContactSurgery
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hsurgery : RlcCentralFaceStrictEntryOriginalContactSurgery
      gamma gamma' rho L)
    {u u' : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    {q' : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u'}
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q') :
    RlcCentralFaceRetainedAnchorTraceIncidence L.boundary := by
  obtain ⟨y, hfirstY, hyLeft⟩ := hsurgery.1 hneg
  obtain ⟨x, hsecondX, hxRight⟩ := hsurgery.2 hpos
  have hfirstSecond :=
    (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable
  exact ⟨⟨x, hfirstSecond.trans hsecondX, hxRight⟩,
    y, hfirstY, hyLeft⟩


theorem rlc_centralFacePIMS_success_of_strictEntryOriginalContactSurgery
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hsurgery : RlcCentralFaceStrictEntryOriginalContactSurgery
      gamma gamma' rho L)
    {u u' : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    {q' : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u'}
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q') :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  obtain ⟨y, hyReach, hyPath⟩ := hsurgery.1 hneg
  obtain ⟨x, hxReachSecond, hxPath⟩ := hsurgery.2 hpos
  have hxReach : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace x :=
    (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable.trans
      hxReachSecond
  have hcomponent : RlcCentralFaceFilledBoundaryGoodComponentContacts
      gamma gamma' rho :=
    ⟨x, y, hxReach.symm.trans hyReach, hxPath, hyPath⟩
  exact rlc_centralFacePIMS_success_of_filledBoundaryContactSegment
    gamma gamma' rho
      (rlc_filledBoundaryContactSegment_of_goodComponentContacts
        gamma gamma' rho hcomponent)


end
end StatMech.Universality
