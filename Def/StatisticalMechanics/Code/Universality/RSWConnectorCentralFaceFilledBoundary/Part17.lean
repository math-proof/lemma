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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part20
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcCentralFaceFilledBoundaryClassifiedBadCarrierSeparationFromLeft
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ x y u v : Site 2,
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        y u ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
      ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Reachable
          v x ∧
      (rlc_dualReflect u ∈ rlc_pathVertices gamma'.1 ∨
        (0 < (rlc_dualReflect u) 0 ∧
          ∃ w ∈ rlc_pathVertices gamma'.1,
            rlc_dualReflect u = rlc_flipX w) ∨
        ((rlc_dualReflect u) 0 < 0 ∧
          ∃ w ∈ rlc_pathVertices gamma.1,
            rlc_dualReflect u = rlc_flipX w) ∨
        ((rlc_dualReflect u) 0 = -2 * n ∨
          (rlc_dualReflect u) 0 = 2 * n ∨
          (rlc_dualReflect u) 1 = -n ∨
          (rlc_dualReflect u) 1 = n))

end
end StatMech.Universality
