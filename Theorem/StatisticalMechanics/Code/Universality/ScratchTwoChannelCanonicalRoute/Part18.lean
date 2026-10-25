/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part16
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_eq_at {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure)
    (eta : RlcTwoChannelEdgeSuccess gamma gamma')
    (rho : RlcTwoChannelTargetFibre
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta) :
    rlc_twoChannelPIMSFixedPayloadConfigOfCapacity hcapacity rho.1 =
      rlc_twoChannelPIMSFixedPayloadConfigAt hcapacity eta rho := by
  rcases rho with ⟨rho, hrho⟩
  subst eta
  rfl

theorem rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_variable_eq {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma') :
    rlc_twoChannelPIMSFixedPayloadConfigOfCapacity hcapacity rho e.1 =
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 e.1 := by
  simp [rlc_twoChannelPIMSFixedPayloadConfigOfCapacity,
    rlc_twoChannelPIMSFixedPayloadConfigAt, e.2]

theorem rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_reserved_open {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
    (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure)
    (rho : RlcTwoChannelEdgeFailure gamma gamma')
    (e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (he : e ∈ rlc_twoChannelOpenEdgeSet
      (rlc_twoChannelCanonicalRoute
        (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1) :
    rlc_twoChannelPIMSFixedPayloadConfigOfCapacity hcapacity rho e = true := by
  unfold rlc_twoChannelPIMSFixedPayloadConfigOfCapacity
    rlc_twoChannelPIMSFixedPayloadConfigAt
  split
  · rename_i hvariable
    have hsubset := rlc_twoChannelCanonicalRoute_open_subset
      (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)
    exact (rlc_mem_twoChannelOpenEdgeSet_iff _ _).mp (hsubset he)
  · simp


end
end StatMech.Universality
