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
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_variable
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullPhysicalVisibleCutTargetGraph gamma gamma' omega ≤
      rlc_twoChannelFullVariableGraph gamma gamma' := by
  intro x y hxy
  obtain ⟨target, htarget, _u, _v, _hsource, _hcross⟩ := hxy
  constructor
  · rw [← SimpleGraph.mem_edgeSet, ← htarget]
    exact target.1.2
  · simpa [← htarget] using target.2


theorem rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_open
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullPhysicalVisibleCutTargetGraph gamma gamma' omega ≤
      FK.openSub (rlc_connectorTwoChannelGraph gamma gamma')
        (rlc_twoChannelEdgeConfigExtend gamma gamma'
          (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega)) := by
  intro x y hxy
  obtain ⟨target, htarget, u, v, hsource, hcross⟩ := hxy
  let source : RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma' :=
    ⟨rlc_twoChannelFullPhysicalSourceEdge target, ⟨target, rfl⟩⟩
  have hclosed : omega source.1 = false :=
    rlc_twoChannelFullPhysical_visibleSource_closed_of_crosses_reachSet
      omega source hsource hcross
  have hopenTarget :
      rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega target.1 =
        true := by
    rw [rlc_twoChannelFullPhysicalPermConfig,
      rlc_twoChannelFullPhysicalEdgePerm_physical]
    rw [show rlc_twoChannelFullPhysicalSourceEdge target = source.1 by rfl]
    rw [hclosed]
    rfl
  rw [FK.openSub_adj]
  constructor
  · rw [← SimpleGraph.mem_edgeSet, ← htarget]
    exact target.1.2
  · have hmem : s(x, y) ∈
        (rlc_connectorTwoChannelGraph gamma gamma').edgeSet := by
      rw [← htarget]
      exact target.1.2
    change (if h : s(x, y) ∈
        (rlc_connectorTwoChannelGraph gamma gamma').edgeSet then
      rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega
        ⟨s(x, y), h⟩ else false) = true
    rw [dif_pos hmem]
    have heq : (⟨s(x, y), hmem⟩ :
        (rlc_connectorTwoChannelGraph gamma gamma').edgeSet) =
        target.1 := Subtype.ext htarget.symm
    rw [heq]
    exact hopenTarget


theorem rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_openFullDual
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma') :
    rlc_twoChannelFullPhysicalVisibleCutTargetGraph gamma gamma' omega ≤
      FK.openSub (rlc_twoChannelFullVariableGraph gamma gamma')
        (rlc_twoChannelFullDualConfig gamma gamma' omega) := by
  intro x y hxy
  have hvariable :=
    rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_variable
      gamma gamma' omega hxy
  obtain ⟨target, htarget, u, v, hsource, hcross⟩ := hxy
  let source : RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma' :=
    ⟨rlc_twoChannelFullPhysicalSourceEdge target, ⟨target, rfl⟩⟩
  have hclosed : omega source.1 = false :=
    rlc_twoChannelFullPhysical_visibleSource_closed_of_crosses_reachSet
      omega source hsource hcross
  rw [FK.openSub_adj]
  constructor
  · exact hvariable
  · have hopen : rlc_twoChannelFullDualConfig gamma gamma' omega
        target.1 = true := by
      rw [rlc_twoChannelFullDualConfig_of_source gamma gamma' omega
        target.1 (rlc_twoChannelFullPhysicalSourceEdge target)
        (rlc_twoChannelFullPhysicalSourceEdge_map target)]
      rw [show rlc_twoChannelFullPhysicalSourceEdge target = source.1 by rfl]
      rw [hclosed]
      rfl
    simpa [← htarget] using hopen


end
end StatMech.Universality
