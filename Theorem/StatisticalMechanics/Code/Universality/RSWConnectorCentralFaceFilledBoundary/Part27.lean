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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part23
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_anchoredSupportedSide_of_anchoredGeometricSide {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hgeom :
      RlcCentralFaceFilledBoundaryAnchoredGeometricSide gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryAnchoredSupportedSide gamma gamma' rho := by
  obtain ⟨B, x, y, hx, hy, hxPath, hyPath, hside⟩ := hgeom
  refine ⟨B, x, y, hx, hy, hxPath, hyPath, ?_⟩
  rcases hside with hordered | hcomplementary
  · left
    refine ⟨hordered.1, ?_⟩
    intro f g hfg
    exact (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma'
        ((rlc_orderedContourArc B.contour hx hy).adj_of_mem_edges hfg).1).1
        (hordered.2 hfg)
  · right
    refine ⟨hcomplementary.1, ?_⟩
    intro f g hfg
    exact (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma'
        ((rlc_complementaryContourArc B.contour hx hy).adj_of_mem_edges hfg).1).1
        (hcomplementary.2 hfg)


end
end StatMech.Universality
