/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorSeededMassCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededOrdinaryAmbient.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_axisGapPIMSSourceSuccessMass {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (q : Real) : Real :=
  FK.bcEventMass (rlc_axisGapFiniteGraph G)
    (rlc_connectorSeparateWiring gamma gamma')
    (BeffaraDC.selfDualPoint q) q
    (rlc_axisGapPIMSMixedReflectedConfig G ⁻¹'
      rlc_finiteAxisGapConnectorEvent G)


def RlcAxisGapPIMSFailureMassTransport {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (q : Real) : Prop :=
  FK.bcEventMass (rlc_axisGapFiniteGraph G)
      (rlc_connectorSeparateWiring gamma gamma')
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteAxisGapConnectorEvent G)ᶜ <=
    rlc_axisGapPIMSSourceSuccessMass G q


end
end StatMech.Universality
