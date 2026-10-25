/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part18
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure RlcTwoChannelPIMSDiscardedPayloadPacking {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') where
  packConfig : RlcTwoChannelEdgeFailure gamma gamma' →
    RlcTwoChannelEdgeConfig gamma gamma'
  variable_eq : ∀ rho
    (e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma'),
    packConfig rho e.1 =
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 e.1
  reserved_open : ∀ rho e,
    e ∈ rlc_twoChannelOpenEdgeSet
        (rlc_twoChannelCanonicalRoute
          (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1 →
      packConfig rho e = true
  injective_on_fibre : ∀ rho sigma,
    rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho =
        rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma →
      packConfig rho = packConfig sigma → rho = sigma


end
end StatMech.Universality
