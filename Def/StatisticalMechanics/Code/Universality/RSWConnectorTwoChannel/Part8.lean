/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelPIMSFailurePushforwardComparison {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Prop :=
  rlc_twoChannelPIMSFailureImageMass gamma gamma' p q ≤
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorMergedWiring gamma gamma') p q
      (rlc_finiteTwoChannelConnectorEvent gamma gamma')


def RlcTwoChannelForcedDualFailurePushforwardComparison {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (q : Real) : Prop :=
  rlc_twoChannelForcedDualFailureImageMass gamma gamma'
      (BeffaraDC.selfDualPoint q) q ≤
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorMergedWiring gamma gamma')
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteTwoChannelConnectorEvent gamma gamma')


end
end StatMech.Universality
