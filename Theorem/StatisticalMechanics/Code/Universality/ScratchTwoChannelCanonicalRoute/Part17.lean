/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part15
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelCanonicalForcedFullPIMSConfig_variable_eq {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    rlc_twoChannelCanonicalForcedFullPIMSConfig hclosure rho e.1 =
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 e.1 := by
  classical
  unfold rlc_twoChannelCanonicalForcedFullPIMSConfig
  split
  · rename_i hroute
    have hsubset := rlc_twoChannelCanonicalRoute_open_subset
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)
    exact (rlc_mem_twoChannelOpenEdgeSet_iff _ _).mp (hsubset hroute) |>.symm
  · rw [rlc_twoChannelFullPIMSConfig_variable_eq_projection,
      ← rlc_twoChannelPIMSEdgeTargetOfClosure_val]

theorem rlc_twoChannelCanonicalForcedFullPIMSConfig_reserved_open {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma') (e :
      (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (he : e ∈ rlc_twoChannelOpenEdgeSet
      (rlc_twoChannelCanonicalRoute
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1) :
    rlc_twoChannelCanonicalForcedFullPIMSConfig hclosure rho e = true := by
  simp [rlc_twoChannelCanonicalForcedFullPIMSConfig, he]


end
end StatMech.Universality
