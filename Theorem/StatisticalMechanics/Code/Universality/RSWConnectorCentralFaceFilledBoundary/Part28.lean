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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part24
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_filledBoundaryContactSegment_of_anchoredGoodComponentContacts
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcomponent :
      RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts
        gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho := by
  obtain ⟨_B, x, y, _hanchor, hx, hy, hxPath, hyPath⟩ := hcomponent
  obtain ⟨px⟩ := hx
  obtain ⟨py⟩ := hy
  let pGood := px.append py
  let hle := rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho
  let p := pGood.mapLe hle
  refine ⟨x, y, p, hxPath, hyPath, ?_⟩
  intro f g hfg
  have hfgGood : s(f, g) ∈ pGood.edges := by
    simpa [p, SimpleGraph.Walk.edges_mapLe_eq_edges] using hfg
  have hgood := (pGood.adj_of_mem_edges hfgGood).2
  exact (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' (pGood.adj_of_mem_edges hfgGood).1.1).1 hgood


theorem rlc_filledBoundaryContactSegment_of_goodComponentContacts
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcomponent :
      RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho := by
  obtain ⟨x, y, hxy, hxPath, hyPath⟩ := hcomponent
  obtain ⟨pGood⟩ := hxy
  let hle := rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho
  let p := pGood.mapLe hle
  refine ⟨x, y, p, hxPath, hyPath, ?_⟩
  intro f g hfg
  have hfgGood : s(f, g) ∈ pGood.edges := by
    simpa [p, SimpleGraph.Walk.edges_mapLe_eq_edges] using hfg
  have hgood := (pGood.adj_of_mem_edges hfgGood).2
  exact (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' (pGood.adj_of_mem_edges hfgGood).1.1).1 hgood

theorem rlc_filledBoundaryContactSegment_of_anchoredSupportedSide {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hside :
      RlcCentralFaceFilledBoundaryAnchoredSupportedSide gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho := by
  obtain ⟨B, x, y, hx, hy, hxPath, hyPath, hside⟩ := hside
  rcases hside with hordered | hcomplementary
  · exact ⟨x, y, rlc_orderedContourArc B.contour hx hy,
      hxPath, hyPath, hordered.2⟩
  · exact ⟨x, y, rlc_complementaryContourArc B.contour hx hy,
      hxPath, hyPath, hcomplementary.2⟩


theorem rlc_boundaryContactArc_of_filledBoundaryContactSegment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hsegment :
      RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho) :
    RlcCentralFaceBoundaryContactArc gamma gamma' rho := by
  obtain ⟨x, y, p, hxPath, hyPath, hpTarget⟩ := hsegment
  let hfill :=
    rlc_connectorCentralFaceFilledFaceBoundaryGraph_le_reachFaceBoundaryGraph
      gamma gamma' rho
  let a := p.mapLe hfill
  refine ⟨x, y, a, hxPath, hyPath, ?_⟩
  dsimp only
  let eta := rlc_connectorCentralFaceAmbientConfig gamma gamma' rho
  let hle := rlc_connectorCentralFaceBoundary_le_openFaceDual gamma gamma' rho
  intro e he
  have hEdges : (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges =
      (a.mapLe hle).edges.map
        (Sym2.map (rlc_dualReflectOpenHom eta)) :=
    SimpleGraph.Walk.edges_map (rlc_dualReflectOpenHom eta) (a.mapLe hle)
  rw [hEdges] at he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  induction e0 using Sym2.inductionOn with
  | _ f g =>
      have hfgA : s(f, g) ∈ a.edges := by
        rwa [SimpleGraph.Walk.edges_mapLe_eq_edges] at he0
      have hfgP : s(f, g) ∈ p.edges := by
        dsimp only [a] at hfgA
        rwa [SimpleGraph.Walk.edges_mapLe_eq_edges] at hfgA
      change s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_connectorCentralFacePlanarEdges gamma gamma'
      exact hpTarget hfgP


theorem rlc_centralFacePIMS_success_of_filledBoundaryContactSegment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hsegment :
      RlcCentralFaceFilledBoundaryContactSegment gamma gamma' rho) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  exact rlc_centralFacePIMS_success_of_boundaryContactArc gamma gamma' rho
    (rlc_boundaryContactArc_of_filledBoundaryContactSegment
      gamma gamma' rho hsegment)


theorem rlc_centralFacePIMS_success_of_anchoredGoodComponentContacts
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcomponent :
      RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts
        gamma gamma' rho) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  exact rlc_centralFacePIMS_success_of_filledBoundaryContactSegment
    gamma gamma' rho
      (rlc_filledBoundaryContactSegment_of_anchoredGoodComponentContacts
        gamma gamma' rho hcomponent)


theorem rlc_centralFacePIMS_success_of_goodComponentContacts
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcomponent :
      RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  exact rlc_centralFacePIMS_success_of_filledBoundaryContactSegment
    gamma gamma' rho
      (rlc_filledBoundaryContactSegment_of_goodComponentContacts
        gamma gamma' rho hcomponent)


theorem rlc_centralFacePIMS_success_of_anchoredGeometricSide {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hgeom :
      RlcCentralFaceFilledBoundaryAnchoredGeometricSide gamma gamma' rho) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  apply rlc_centralFacePIMS_success_of_filledBoundaryContactSegment
    gamma gamma' rho
  apply rlc_filledBoundaryContactSegment_of_anchoredSupportedSide
  exact rlc_anchoredSupportedSide_of_anchoredGeometricSide
    gamma gamma' rho hgeom


end
end StatMech.Universality
