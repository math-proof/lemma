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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part35
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem RlcCentralFaceNegativeStrictWallEntryDecompAt.nonwallGoodContourEdge
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
        rlc_connectorFourTraceEdges gamma gamma' := by
  obtain ⟨_A, a, b, _pA, _p, _r, hab, _hdecomp, _hAzero,
    _hAoff, hentryNot, _hrNeg, _hrNoLeft, _hrRight,
    _hrNotNil⟩ := hentry
  refine ⟨a, b, L.boundary.contour_covers s(a, b) ?_, hab.2,
    hentryNot⟩
  rw [SimpleGraph.mem_edgeSet]
  exact hab.1


end
end StatMech.Universality
