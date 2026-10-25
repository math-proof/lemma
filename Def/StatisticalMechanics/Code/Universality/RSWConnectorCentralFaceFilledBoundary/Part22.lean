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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part25
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcCentralFaceLowestAnchorComplementaryCrossingBelow {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) : Prop :=
  ∃ (a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace)
    (f g : Site 2) (k : Int),
    s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧
      (∀ e ∈ a.edges, e ∈ L.boundary.contour.edges) ∧
      s(f, g) ∈ a.edges ∧
      s(rlc_dualReflect f, rlc_dualReflect g) =
        s((![-1, k] : Site 2), ![0, k]) ∧
      k ≤ (gamma.1.1 : Site 2) 1

def RlcCentralFaceLowestAnchorComplementaryCrossingAbove {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho) : Prop :=
  ∃ (a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace)
    (f g : Site 2) (k : Int),
    s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges ∧
      (∀ e ∈ a.edges, e ∈ L.boundary.contour.edges) ∧
      s(f, g) ∈ a.edges ∧
      s(rlc_dualReflect f, rlc_dualReflect g) =
        s((![-1, k] : Site 2), ![0, k]) ∧
      L.boundary.height + 1 < k

def RlcCentralFaceLowestAnchorLowerOrderBadExit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho,
    RlcCentralFaceLowestAnchorOrderedBadExitAt gamma gamma' rho L ∧
      RlcCentralFaceLowestAnchorComplementaryCrossingBelow
        gamma gamma' rho L

def RlcCentralFaceLowestAnchorUpperOrderBadExit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho,
    RlcCentralFaceLowestAnchorOrderedBadExitAt gamma gamma' rho L ∧
      RlcCentralFaceLowestAnchorComplementaryCrossingAbove
        gamma gamma' rho L


end
end StatMech.Universality
