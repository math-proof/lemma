/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFibreCube.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelVisibleFibreHall.Part2
open Finset SimpleGraph Set


namespace StatMech.Universality

noncomputable section

noncomputable def rlc_twoChannelPIMSFixedEquivDiscarded {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    RlcTwoChannelPIMSFixedTargetEdge gamma gamma' ≃
      RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' where
  toFun e := ⟨rlc_twoChannelPIMSEdgePerm gamma gamma' e.1, by
    rintro ⟨v, hv⟩
    apply e.2
    have heq : e.1 = v.1 := by
      apply (rlc_twoChannelPIMSEdgePerm gamma gamma').injective
      rw [rlc_twoChannelPIMSEdgePerm_variable]
      exact hv.symm
    rw [heq]
    exact v.2⟩
  invFun e := ⟨(rlc_twoChannelPIMSEdgePerm gamma gamma').symm e.1, by
    intro hcentral
    let v : RlcTwoChannelPIMSVariableTargetEdge gamma gamma' :=
      ⟨(rlc_twoChannelPIMSEdgePerm gamma gamma').symm e.1, hcentral⟩
    apply e.2
    refine ⟨v, ?_⟩
    rw [← rlc_twoChannelPIMSEdgePerm_variable v]
    exact (rlc_twoChannelPIMSEdgePerm gamma gamma').apply_symm_apply e.1⟩
  left_inv e := by
    apply Subtype.ext
    exact (rlc_twoChannelPIMSEdgePerm gamma gamma').symm_apply_apply e.1
  right_inv e := by
    apply Subtype.ext
    exact (rlc_twoChannelPIMSEdgePerm gamma gamma').apply_symm_apply e.1


def rlc_twoChannelConfigOfVisibleFixed {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (base : RlcTwoChannelPIMSVisibleBase gamma gamma')
    (bits : ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma')) :
    RlcTwoChannelEdgeConfig gamma gamma' :=
  fun e => if hvariable : rlc_pimsEdgeEquiv (e.1.map Subtype.val) ∈
      rlc_connectorCentralFaceEdges gamma gamma' then
    base ⟨e, hvariable⟩
  else
    bits ⟨e, hvariable⟩

end
end StatMech.Universality
