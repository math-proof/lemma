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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part44
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

def RlcCentralFacePairedTerminalSideChange {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (u v u' v' : Site 2) : Prop :=
  ∃ (t h t' h' : Site 2),
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t u ∧
    s(rlc_dualReflect t, rlc_dualReflect u) ∈
      rlc_reflectedPathEdges gamma.1 ∧
    h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
    h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) ∧
    s(rlc_dualReflect u, rlc_dualReflect v) ∉
      rlc_connectorFourTraceEdges gamma gamma' ∧
    rlc_dualReflect u ∈ rlc_connectorBox n ∧
    rlc_dualReflect v ∈ rlc_connectorBox n ∧
    (∀ k ∈ rlc_connectorCentralFaceRegion gamma gamma',
      k ∉ flankFaces (rlc_dualReflect u) (rlc_dualReflect v)) ∧
    (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj t' u' ∧
    s(rlc_dualReflect t', rlc_dualReflect u') ∈
      rlc_reflectedPathEdges gamma'.1 ∧
    h' ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
    h' ∈ flankFaces (rlc_dualReflect t') (rlc_dualReflect u') ∧
    s(rlc_dualReflect u', rlc_dualReflect v') ∉
      rlc_connectorFourTraceEdges gamma gamma' ∧
    rlc_dualReflect u' ∈ rlc_connectorBox n ∧
    rlc_dualReflect v' ∈ rlc_connectorBox n ∧
    (∀ k ∈ rlc_connectorCentralFaceRegion gamma gamma',
      k ∉ flankFaces (rlc_dualReflect u') (rlc_dualReflect v')) ∧
    ∃ (hhBox : h ∈ rlc_connectorFaceBox n)
      (hh'Box : h' ∈ rlc_connectorFaceBox n),
      (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
          ⟨h, hhBox⟩ ⟨h', hh'Box⟩ ∧
      ∃ k k' : Site 2,
        flankFaces (rlc_dualReflect t) (rlc_dualReflect u) = s(h, k) ∧
        flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧
        (let C := (L.boundary.contour.mapLe
          (faceBoundaryGraph_le
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
              rlc_dualReflectLatticeHom
         (((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C) ∧
              phb_doubleDualEquiv.symm k ∉ jec_leftRegion C) ∨
            (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
              phb_doubleDualEquiv.symm k ∈ jec_leftRegion C))) ∧
        (let C := (L.boundary.contour.mapLe
          (faceBoundaryGraph_le
            (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
              rlc_dualReflectLatticeHom
         (((phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C) ∧
              phb_doubleDualEquiv.symm k' ∉ jec_leftRegion C) ∨
            (phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C ∧
              phb_doubleDualEquiv.symm k' ∈ jec_leftRegion C)))


end
end StatMech.Universality
