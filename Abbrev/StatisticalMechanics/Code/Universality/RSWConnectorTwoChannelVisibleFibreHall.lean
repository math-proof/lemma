/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelVisibleFibreHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part43
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

abbrev RlcTwoChannelPIMSVisibleBase {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :=
  ConfigSpace (RlcTwoChannelPIMSVariableTargetEdge gamma gamma')


end
end StatMech.Universality
