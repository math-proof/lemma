/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelClosureFailureCertificate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  ∀ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    rho ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma' →
      rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
        rlc_finiteCentralFaceClosureConnectorEvent gamma gamma'


def RlcCentralFaceClosureFailureCertificate {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) : Prop :=
  ∀ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma' →
      rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
        rlc_finiteCentralFaceClosureConnectorEvent gamma gamma'


end
end StatMech.Universality
