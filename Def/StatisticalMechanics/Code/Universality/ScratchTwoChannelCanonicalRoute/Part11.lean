/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part12
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_twoChannelCanonicalRouteAvailable {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (route : (rlc_twoChannelCanonicalRoutePlan gamma gamma').Route) : Prop :=
  route = rlc_twoChannelCanonicalRoute (target rho)

end
end StatMech.Universality
