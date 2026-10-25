/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part17
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem RlcTwoChannelPIMSDiscardedPayloadPacking.target_eq_of_pack_eq
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure)
    {rho sigma : RlcTwoChannelEdgeFailure gamma gamma'}
    (hpack : packing.packConfig rho = packing.packConfig sigma) :
    rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho =
      rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma := by
  apply Subtype.ext
  funext e
  by_cases hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
      rlc_connectorCentralFaceEdges gamma gamma'
  · let vtarget : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
      ⟨e, hvariable⟩
    exact (packing.variable_eq rho vtarget).symm.trans
      ((congrFun hpack e).trans (packing.variable_eq sigma vtarget))
  · let ftarget : RlcTwoChannelPIMSFixedTargetEdge gamma gamma' :=
      ⟨e, hvariable⟩
    simpa only [rlc_twoChannelPIMSEdgeTargetOfClosure_val] using
      rlc_twoChannelPIMSEdgeProjection_fixedTarget_eq rho.1 sigma.1 ftarget

theorem RlcTwoChannelPIMSDiscardedPayloadPacking.packConfig_success
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    rlc_twoChannelEdgeConfigExtend gamma gamma' (packing.packConfig rho) ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  apply (rlc_twoChannelCanonicalRoutePlan gamma gamma').success_of_reserved
    (rlc_twoChannelCanonicalRoute
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho))
  exact packing.reserved_open rho

end
end StatMech.Universality
