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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part34
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcCentralFacePositiveReflectedLeftAxisSuffixAt {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (u : Site 2) : Prop :=
  ∃ (c : Site 2)
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk c u),
    rlc_dualReflect c = (gamma'.1.2.1 : Site 2) ∧
      (∀ x ∈ q.support,
        rlc_dualReflect x ∉ rlc_pathVertices gamma.1) ∧
      ∀ {f g : Site 2}, s(f, g) ∈ q.edges →
        s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_reflectedPathEdges gamma'.1


def RlcCentralFacePositiveStrictWallEntryAt {n : Int}
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
      (∀ x ∈ r.support, 0 < (rlc_dualReflect x) 0) ∧
      (∀ x ∈ r.support,
        rlc_dualReflect x ∉ rlc_pathVertices gamma.1) ∧
      (∀ {f g : Site 2}, s(f, g) ∈ r.edges →
        s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_reflectedPathEdges gamma'.1) ∧
      ¬ r.Nil


end
end StatMech.Universality
