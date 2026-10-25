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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalPermConfig_injective {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n} :
    Function.Injective
      (rlc_twoChannelFullPhysicalPermConfig gamma gamma') := by
  intro rho sigma hconfig
  funext source
  have h := congrFun hconfig
    ((rlc_twoChannelFullPhysicalEdgePerm gamma gamma').symm source)
  simp only [rlc_twoChannelFullPhysicalPermConfig,
    Equiv.apply_symm_apply] at h
  exact Bool.not_injective h


theorem rlc_twoChannelFullPhysicalPermConfig_eq_fullDual {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma') :
    rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega target.1 =
      rlc_twoChannelFullDualConfig gamma gamma' omega target.1.1 := by
  rw [rlc_twoChannelFullPhysicalPermConfig,
    rlc_twoChannelFullPhysicalEdgePerm_physical,
    rlc_twoChannelFullDualConfig_of_source gamma gamma' omega target.1.1
      (rlc_twoChannelFullPhysicalSourceEdge target)
      (rlc_twoChannelFullPhysicalSourceEdge_map target)]


theorem rlc_twoChannelFullPhysicalPermConfig_targetOfVisibleSource
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (source : RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma') :
    rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega
        (rlc_twoChannelFullPhysicalTargetOfVisibleSource source).1 =
      !(omega source.1) := by
  rw [rlc_twoChannelFullPhysicalPermConfig,
    rlc_twoChannelFullPhysicalEdgePerm_physical,
    rlc_twoChannelFullPhysicalSourceEdge_targetOfVisibleSource]


end
end StatMech.Universality
