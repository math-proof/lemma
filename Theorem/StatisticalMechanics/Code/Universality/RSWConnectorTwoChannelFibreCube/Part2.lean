/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFibreCube.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelVisibleFibreHall.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

theorem rlc_twoChannelConfigOfFailureComplement_eq_fullPIMS {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
    (rho : RlcTwoChannelEdgeFailure gamma gamma') :
    rlc_twoChannelConfigOfVisibleFixed
        (rlc_twoChannelFailureVisibleBase hclosure rho)
        (rlc_twoChannelFailureComplementFixedBits rho) =
      rlc_twoChannelFullPIMSConfig gamma gamma' rho.1 := by
  funext e
  by_cases hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
      rlc_connectorCentralFaceEdges gamma gamma'
  · let v : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
      ⟨e, hvariable⟩
    rw [show rlc_twoChannelConfigOfVisibleFixed
        (rlc_twoChannelFailureVisibleBase hclosure rho)
        (rlc_twoChannelFailureComplementFixedBits rho) e =
      rlc_twoChannelFailureVisibleBase hclosure rho v by
        exact rlc_twoChannelConfigOfVisibleFixed_variable _ _ v]
    change (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 v.1 = _
    rw [rlc_twoChannelPIMSEdgeTargetOfClosure_val]
    exact (rlc_twoChannelFullPIMSConfig_variable_eq_projection rho.1 v).symm
  · let f : RlcTwoChannelPIMSFixedTargetEdge gamma gamma' := ⟨e, hvariable⟩
    rw [show rlc_twoChannelConfigOfVisibleFixed
        (rlc_twoChannelFailureVisibleBase hclosure rho)
        (rlc_twoChannelFailureComplementFixedBits rho) e =
      rlc_twoChannelFailureComplementFixedBits rho f by
        exact rlc_twoChannelConfigOfVisibleFixed_fixed _ _ f]
    rfl


end
end StatMech.Universality
