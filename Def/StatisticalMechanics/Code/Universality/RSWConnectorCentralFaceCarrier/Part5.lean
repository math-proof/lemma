/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_connectorCentralFaceRegionSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (Site 2) :=
  {f | ∃ (hf : f ∈ rlc_connectorFaceBox n)
      (hs : rlc_connectorCentralFace ∈ rlc_connectorFaceBox n),
    (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
      ⟨rlc_connectorCentralFace, hs⟩ ⟨f, hf⟩}

end
end StatMech.Universality
