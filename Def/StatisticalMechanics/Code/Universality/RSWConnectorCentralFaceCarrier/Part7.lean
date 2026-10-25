/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorCentralFaceClosureEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  (edgesWithinFinset (rlc_connectorBox n)).filter fun e =>
    ∃ f ∈ rlc_connectorCentralFaceRegion gamma gamma',
      f ∈ fci_faceEdgeEquiv.symm e


noncomputable def rlc_connectorCentralFaceEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  rlc_connectorCentralFaceClosureEdges gamma gamma' \
    rlc_connectorFourTraceEdges gamma gamma'


noncomputable def rlc_connectorCentralFacePlanarEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Finset (Sym2 (Site 2)) :=
  rlc_connectorCentralFaceClosureEdges gamma gamma' ∪
    rlc_connectorFourTraceEdges gamma gamma'

end
end StatMech.Universality
