/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part18
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem RlcTwoChannelPIMSDiscardedPayloadPacking.embedding_compatible
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    (rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible
      (rlc_twoChannelCanonicalRouteAvailable
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure)) rho
      (packing.embedding rho) := by
  let route := rlc_twoChannelCanonicalRoute
    (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)
  refine ⟨route, rfl, ?_⟩
  constructor
  · exact packing.reserved_open rho
  · intro e hreserved hpayload
    exfalso
    apply hpayload
    change e ∈ Finset.univ \ rlc_twoChannelOpenEdgeSet route.1
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ e, hreserved⟩

theorem RlcTwoChannelPIMSDiscardedPayloadPacking.hasCodeHall
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure) :
    (rlc_twoChannelCanonicalRoutePlan gamma gamma').HasCodeHall
      (rlc_twoChannelCanonicalRouteAvailable
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure)) := by
  apply (rlc_twoChannelEdgeCodeHall_iff_exists_compatibleEmbedding
    gamma gamma'
    ((rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible
      (rlc_twoChannelCanonicalRouteAvailable
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure)))).mpr
  exact ⟨packing.embedding, packing.embedding_compatible⟩


end
end StatMech.Universality
