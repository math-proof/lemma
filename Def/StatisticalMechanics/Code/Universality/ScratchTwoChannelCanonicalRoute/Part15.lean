/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part16
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelCanonicalForcedFullPIMSConfig {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    RlcTwoChannelEdgeConfig gamma gamma' :=
  fun e =>
    if e ∈ rlc_twoChannelOpenEdgeSet
        (rlc_twoChannelCanonicalRoute
          (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1 then
      true
    else
      rlc_twoChannelFullPIMSConfig gamma gamma' rho.1 e

end
end StatMech.Universality
