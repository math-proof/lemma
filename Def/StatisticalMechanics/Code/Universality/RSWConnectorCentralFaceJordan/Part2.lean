/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceJordan.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_connectorCentralFaceReachSet {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Set (Site 2) :=
  {z | ∃ hz : z ∈ rect (-2 * n) (2 * n) (-n) n,
    ConnectedWithin 2 (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)
      (rect (-2 * n) (2 * n) (-n) n)
      ⟨(rlc_connectorRightAnchor gamma : Site 2),
        (rlc_connectorRightAnchor gamma).2⟩ ⟨z, hz⟩}

end
end StatMech.Universality
