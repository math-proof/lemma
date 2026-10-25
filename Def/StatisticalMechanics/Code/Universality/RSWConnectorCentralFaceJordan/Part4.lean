/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part3
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcCentralFaceBoundaryContactArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (x y : Site 2)
    (a : (faceBoundaryGraph
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Walk x y),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      let eta := rlc_connectorCentralFaceAmbientConfig gamma gamma' rho
      let hle := rlc_connectorCentralFaceBoundary_le_openFaceDual gamma gamma' rho
      ∀ e ∈ (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges,
        e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma'


def RlcCentralFaceWalkContactSegment {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {f g : Site 2}
    (a : (faceBoundaryGraph
      (rlc_connectorCentralFaceReachSet gamma gamma' rho)).Walk f g) : Prop :=
  ∃ (x y : Site 2) (hx : x ∈ a.support) (hy : y ∈ a.support),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      let eta := rlc_connectorCentralFaceAmbientConfig gamma gamma' rho
      let hle := rlc_connectorCentralFaceBoundary_le_openFaceDual gamma gamma' rho
      ∀ e ∈ (rlc_dualReflectOpenWalk eta
        ((rlc_centralFaceContactSubwalk a hx hy).mapLe hle)).edges,
        e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma'


end
end StatMech.Universality
