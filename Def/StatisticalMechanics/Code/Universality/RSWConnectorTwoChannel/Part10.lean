/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part8
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFailureMassComparison {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Prop :=
  FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorSeparateWiring gamma gamma') p q
      (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤
    FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma')
      (rlc_connectorMergedWiring gamma gamma') p q
      (rlc_finiteTwoChannelConnectorEvent gamma gamma')


end
end StatMech.Universality
