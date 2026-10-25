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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part32
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcCentralFacePositiveWallRunSurgeryAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u : Site 2) : Prop :=
  ∃ (A a b : Site 2)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A a)
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u)
    (hab : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b),
    rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      (rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∨
        rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma') ∧
      s(rlc_dualReflect a, rlc_dualReflect b) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (∀ e ∈ r.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma') ∧
      ¬ r.Nil ∧
      ∃ w ∈ rlc_pathVertices gamma'.1,
        rlc_dualReflect u = rlc_flipX w


def RlcCentralFacePositiveAxisAllWallRunAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u : Site 2) : Prop :=
  ∃ (A : Site 2)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A u),
      rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      rlc_dualReflect A ∈ rlc_pathVertices gamma'.1 ∧
      (∀ e ∈ p.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma') ∧
      ∃ w ∈ rlc_pathVertices gamma'.1,
        rlc_dualReflect u = rlc_flipX w


end
end StatMech.Universality
