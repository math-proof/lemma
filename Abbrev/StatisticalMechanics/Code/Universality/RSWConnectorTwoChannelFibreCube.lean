/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFibreCube.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelVisibleFibreHall.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

abbrev RlcTwoChannelSuccessFixedPayload {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma') :=
  {bits : ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma') //
    rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelConfigOfVisibleFixed base bits) ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma'}


end
end StatMech.Universality
