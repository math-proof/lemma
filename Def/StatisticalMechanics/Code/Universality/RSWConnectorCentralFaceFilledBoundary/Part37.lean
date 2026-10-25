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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part40
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcCentralFaceAnchoredNonwallGoodContourEdgeMissingContactIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (f g : Site 2) : Prop :=
  s(f, g) ∈ B.contour.edges ∧
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
    s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_connectorFourTraceEdges gamma gamma' ∧
    (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace f ∧
    (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace g ∧
    ((∀ x : Site 2,
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 →
          ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
              gamma gamma' rho).Reachable B.firstFace x) ∨
      ∃ x : Site 2,
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable B.firstFace x ∧
        ∀ y : Site 2,
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 →
            ¬ (rlc_connectorCentralFaceGoodBoundaryGraph
                gamma gamma' rho).Reachable B.firstFace y)


end
end StatMech.Universality
