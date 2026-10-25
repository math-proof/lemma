/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelScoreAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FiniteActiveDuality.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part86
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelScoreAudit
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalPermutationScoreDefect_iff_eulerScoreBound
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) (N : Nat) :
    RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N ↔
      RlcTwoChannelFullPhysicalEulerScoreBound gamma gamma' N := by
  constructor <;> intro h rho
  · have hopen : FK.openCount
        (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) ≤
          (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card := by
      unfold FK.openCount
      exact Finset.card_filter_le _ _
    have hscore := h rho
    rw [rlc_twoChannelFullPhysicalPermConfig_openCount] at hscore
    omega
  · have hopen : FK.openCount
        (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigExtend gamma gamma' rho.1) ≤
          (rlc_connectorTwoChannelGraph gamma gamma').edgeFinset.card := by
      unfold FK.openCount
      exact Finset.card_filter_le _ _
    have heuler := h rho
    rw [rlc_twoChannelFullPhysicalPermConfig_openCount]
    omega

end
end StatMech.Universality
