/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Abbrev.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_connectorFiniteFaceCutGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorFaceVertex n) :=
  (rlc_connectorFourTraceFaceCutGraph gamma gamma').induce
    (rlc_connectorFaceBox n : Set (Site 2))

end
end StatMech.Universality
