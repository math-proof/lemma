/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part46
import Theorem.StatisticalMechanics.Code.Foundations.WeightedFiniteInjection
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannel.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelPIMSFailureImageMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  ∑ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ.indicator
      (fun _ => (1 : Real)) rho *
        (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
          (fun _ => (1 : Real))
          (rlc_connectorCentralFacePIMSConfig gamma gamma' rho) *
        FK.bcProb (rlc_connectorTwoChannelGraph gamma gamma')
          (rlc_connectorSeparateWiring gamma gamma') p q rho


noncomputable def rlc_twoChannelForcedDualFailureImageMass {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p q : Real) : Real :=
  ∑ rho : ConfigSpace (Sym2 (RlcConnectorVertex n)),
    (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ.indicator
      (fun _ => (1 : Real)) rho *
        (rlc_finiteTwoChannelConnectorEvent gamma gamma').indicator
          (fun _ => (1 : Real))
          (rlc_connectorCentralFacePIMSConfig gamma gamma' rho) *
        rlc_twoChannelForcedDualProb gamma gamma' p q rho


end
end StatMech.Universality
