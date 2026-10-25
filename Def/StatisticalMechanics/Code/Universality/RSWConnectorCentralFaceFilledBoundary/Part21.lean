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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part24
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcCentralFaceLowestAnchorOrderedBadExitAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) : Prop :=
  ∃ (x y z : Site 2)
    (p : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace z)
    (u v : Site 2)
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u),
    x ∈ L.boundary.contour.support ∧
      y ∈ L.boundary.contour.support ∧
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      (z = x ∨ z = y) ∧
      (∀ e ∈ p.edges, e ∈ L.boundary.contour.edges) ∧
      (∀ e ∈ q.edges, e ∈ p.edges) ∧
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
      s(u, v) ∈ p.edges ∧
      ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v ∧
      (rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' ∨
        (rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n)

def RlcCentralFaceLowestAnchorOrderedBadExit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho,
    RlcCentralFaceLowestAnchorOrderedBadExitAt gamma gamma' rho L


end
end StatMech.Universality
