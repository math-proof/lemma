/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part9
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_twoChannelSuccessfulSubconfigs {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (eta : RlcTwoChannelEdgeSuccess gamma gamma') :
    Finset (RlcTwoChannelEdgeSuccess gamma gamma') :=
  Finset.univ.filter fun route =>
    rlc_twoChannelOpenEdgeSet route.1 ⊆
      rlc_twoChannelOpenEdgeSet eta.1

end
end StatMech.Universality
