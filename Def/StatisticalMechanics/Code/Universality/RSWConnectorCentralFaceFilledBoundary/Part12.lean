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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part15
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcCentralFaceFilledBoundaryAnchoredSupportedSide {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (x y : Site 2) (hx : x ∈ B.contour.support)
    (hy : y ∈ B.contour.support),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      ((B.firstFace ∈
            (rlc_orderedContourArc B.contour hx hy).support ∧
          ∀ {f g : Site 2},
            s(f, g) ∈ (rlc_orderedContourArc B.contour hx hy).edges →
              s(rlc_dualReflect f, rlc_dualReflect g) ∈
                rlc_connectorCentralFacePlanarEdges gamma gamma') ∨
        (B.firstFace ∈
            (rlc_complementaryContourArc B.contour hx hy).support ∧
          ∀ {f g : Site 2},
            s(f, g) ∈
                (rlc_complementaryContourArc B.contour hx hy).edges →
              s(rlc_dualReflect f, rlc_dualReflect g) ∈
                rlc_connectorCentralFacePlanarEdges gamma gamma'))


def RlcCentralFaceReflectedEdgeCarrierGeometry {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f g : Site 2) : Prop :=
  s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_connectorFourTraceEdges gamma gamma' ∨
    (rlc_dualReflect f ∈ rlc_connectorBox n ∧
      rlc_dualReflect g ∈ rlc_connectorBox n ∧
      ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
        h ∈ flankFaces (rlc_dualReflect f) (rlc_dualReflect g))

end
end StatMech.Universality
