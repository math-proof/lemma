/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorMassDualityCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part75
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcConnectorPIMSFailureMassTransport {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (q : Real) : Prop :=
  rlc_connectorForcedDualEventMass gamma gamma'
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteConnectorEvent gamma gamma')ᶜ <=
    rlc_connectorForcedDualEventMass gamma gamma'
      (BeffaraDC.selfDualPoint q) q
      (rlc_connectorPIMSReflectedConfig gamma gamma' ⁻¹'
        rlc_finiteConnectorEvent gamma gamma')


def RlcConnectorPIMSCollaredFailureMassTransport {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (q : Real) : Prop :=
  rlc_connectorForcedDualEventMass gamma gamma'
      (BeffaraDC.selfDualPoint q) q
      (rlc_finiteConnectorEvent gamma gamma')ᶜ <=
    rlc_connectorForcedDualEventMass gamma gamma'
      (BeffaraDC.selfDualPoint q) q
      (rlc_connectorPIMSCollaredReflectedConfig gamma gamma' ⁻¹'
        rlc_finiteConnectorEvent gamma gamma')


end
end StatMech.Universality
