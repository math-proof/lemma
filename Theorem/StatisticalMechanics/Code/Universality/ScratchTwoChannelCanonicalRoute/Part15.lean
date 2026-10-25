/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part13
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma') :
    RlcCentralFaceClosureFailureCertificate gamma gamma' := by
  intro rho hno
  obtain ⟨L, hL⟩ := hinc.2 rho hno
  exact rlc_centralFacePIMS_success_of_retainedAnchorTraceIncidence
    gamma gamma' rho hL


end
end StatMech.Universality
