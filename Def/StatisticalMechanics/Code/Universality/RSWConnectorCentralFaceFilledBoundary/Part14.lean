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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part17
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (x y : Site 2),
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj
        B.firstFace B.secondFace ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        x B.firstFace ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        B.firstFace y ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1


def RlcCentralFaceFilledBoundaryGoodComponentContacts {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ x y : Site 2,
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        x y ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1


def RlcCentralFaceFilledBoundaryBadCarrierSeparation {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ x y u v : Site 2,
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        x u ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
      ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
          v y


end
end StatMech.Universality
