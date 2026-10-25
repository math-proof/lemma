/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelVisibleFibreHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part43
import Abbrev.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelVisibleFibreHall
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

def rlc_twoChannelFailureVisibleBase {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    RlcTwoChannelPIMSVisibleBase gamma gamma' :=
  fun e => (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 e.1


def rlc_twoChannelSuccessVisibleBase {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    RlcTwoChannelPIMSVisibleBase gamma gamma' :=
  fun e => eta.1 e.1

end
end StatMech.Universality
