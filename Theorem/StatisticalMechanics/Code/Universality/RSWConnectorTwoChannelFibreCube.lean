/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFibreCube.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelVisibleFibreHall.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

@[simp] theorem rlc_twoChannelConfigOfVisibleFixed_variable {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma')
    (bits : ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma'))
    (e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    rlc_twoChannelConfigOfVisibleFixed base bits e.1 = base e := by
  simp [rlc_twoChannelConfigOfVisibleFixed, e.2]

@[simp] theorem rlc_twoChannelConfigOfVisibleFixed_fixed {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma')
    (bits : ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma'))
    (e : RlcTwoChannelPIMSFixedTargetEdge gamma gamma') :
    rlc_twoChannelConfigOfVisibleFixed base bits e.1 = bits e := by
  simp [rlc_twoChannelConfigOfVisibleFixed, e.2]


end
end StatMech.Universality
