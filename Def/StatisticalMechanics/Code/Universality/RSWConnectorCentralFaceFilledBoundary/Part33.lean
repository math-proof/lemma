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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part36
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcCentralFaceStrictReflectedBarrierResidue {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) : Prop :=
  ∃ z : Site 2,
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        L.boundary.firstFace z ∧
      ((0 < (rlc_dualReflect z) 0 ∧
          ∃ w ∈ rlc_pathVertices gamma'.1,
            rlc_dualReflect z = rlc_flipX w) ∨
        ((rlc_dualReflect z) 0 < 0 ∧
          ∃ w ∈ rlc_pathVertices gamma.1,
            rlc_dualReflect z = rlc_flipX w))


def RlcCentralFaceStrictSurgeryResidue {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u u' : Site 2) : Prop :=
  RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u ∨
    RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u' ∨
    RlcCentralFaceStrictReflectedBarrierResidue gamma gamma' rho L


end
end StatMech.Universality
