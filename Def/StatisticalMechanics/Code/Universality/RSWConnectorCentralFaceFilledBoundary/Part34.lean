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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part37
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcCentralFacePositiveStrictCarrierSurgeryAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u v : Site 2) : Prop :=
  RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u ∧
    (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
    ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v


def RlcCentralFaceNegativeStrictCarrierSurgeryAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u v : Site 2) : Prop :=
  RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u ∧
    (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v ∧
    ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v


def RlcCentralFaceStrictCarrierSurgeryResidue {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u v u' v' : Site 2) : Prop :=
  RlcCentralFaceNegativeStrictCarrierSurgeryAt
      gamma gamma' rho L u v ∨
    RlcCentralFacePositiveStrictCarrierSurgeryAt
      gamma gamma' rho L u' v' ∨
    RlcCentralFaceStrictReflectedBarrierResidue gamma gamma' rho L


def RlcCentralFaceNegativeWallRunDecompAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {u : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u) : Prop :=
  ∃ (A a b : Site 2)
    (pA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A L.boundary.firstFace)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A a)
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u)
    (hab : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b),
    pA.append q = p.append (.cons hab r) ∧
      rlc_dualReflect A = (![0, L.boundary.height + 1] : Site 2) ∧
      rlc_dualReflect A ∉ rlc_connectorBarrier gamma gamma' ∧
      s(rlc_dualReflect a, rlc_dualReflect b) ∉
        rlc_connectorFourTraceEdges gamma gamma' ∧
      (∀ e ∈ r.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma') ∧
      ¬ r.Nil ∧
      ∃ w ∈ rlc_pathVertices gamma.1,
        rlc_dualReflect u = rlc_flipX w


def RlcCentralFacePositiveWallRunDecompAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {u : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u) : Prop :=
  ∃ (A a b : Site 2)
    (pA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A L.boundary.firstFace)
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk A a)
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk b u)
    (hanchor : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Adj L.boundary.firstFace L.boundary.secondFace)
    (hab : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b),
    pA.append (.cons hanchor q) = p.append (.cons hab r) ∧
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


end
end StatMech.Universality
