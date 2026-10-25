/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part11
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelCanonicalRoute_target_compatible {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (target : RlcTwoChannelEdgeFailure gamma gamma' →
      RlcTwoChannelEdgeSuccess gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    (rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible
      (rlc_twoChannelCanonicalRouteAvailable target) rho (target rho) := by
  refine ⟨rlc_twoChannelCanonicalRoute (target rho), rfl, ?_⟩
  exact rlc_twoChannelCanonicalRoute_target_mem_codeSet (target rho)


end
end StatMech.Universality
