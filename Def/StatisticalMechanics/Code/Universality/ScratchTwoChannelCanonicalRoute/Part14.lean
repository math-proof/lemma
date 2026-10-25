/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part15
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_twoChannelPIMSEdgeTargetOfClosure {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    RlcTwoChannelEdgeSuccess gamma gamma' := by
  let source := rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1
  let target := rlc_connectorCentralFacePIMSConfig gamma gamma' source
  let targetEdge := (rlc_twoChannelConfigSplitEquiv gamma gamma' target).1
  refine ⟨targetEdge, ?_⟩
  apply (rlc_twoChannel_split_fst_mem_event_iff gamma gamma' target).mpr
  exact rlc_twoChannelPIMS_success_of_closureFailureCertificate
    gamma gamma' hclosure source rho.2

end
end StatMech.Universality
