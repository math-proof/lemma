/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelForcedDualZ {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  ∑ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    BeffaraDC.pfdDualWeight P p q
      (FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma' rho))

noncomputable def rlc_twoChannelForcedDualProb {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Real :=
  let P := rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'
  BeffaraDC.pfdDualWeight P p q
      (FK.openSub P.G (rlc_connectorForceTraceConfig gamma gamma' rho)) /
    rlc_twoChannelForcedDualZ gamma gamma' p q

end
end StatMech.Universality
