/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalPermConfig_success_of_variableConnector
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hvariable : RlcTwoChannelFullVariableConnectorSuccess
      gamma gamma' omega) :
    rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega) ∈
      rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hvariable
  refine ⟨x, y, hx, hy, hxy.mono ?_⟩
  intro u v huv
  rw [FK.openSub_adj] at huv ⊢
  let target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' :=
    ⟨⟨s(u, v), huv.1.1⟩, huv.1.2⟩
  refine ⟨huv.1.1, ?_⟩
  have hmem : s(u, v) ∈
      (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
    (SimpleGraph.mem_edgeSet _).mpr huv.1.1
  change (if h : s(u, v) ∈
      (rlc_connectorTwoChannelGraph gamma gamma').edgeSet then
    rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega
      ⟨s(u, v), h⟩ else false) = true
  rw [dif_pos hmem]
  rw [show (⟨s(u, v), hmem⟩ :
      (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) = target.1 by rfl]
  rw [rlc_twoChannelFullPhysicalPermConfig_eq_fullDual]
  exact huv.2


end
end StatMech.Universality
