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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part8
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_right_mem_visibleRightReachSet
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x : RlcConnectorVertex n} (hx : rlc_connectorOnRight gamma x) :
    x ∈ rlc_twoChannelFullPhysicalVisibleRightReachSet
      gamma gamma' omega :=
  ⟨x, hx, Reachable.refl _⟩


theorem rlc_twoChannelFullPhysical_left_not_mem_visibleRightReachSet_of_failure
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {y : RlcConnectorVertex n} (hy : rlc_connectorOnLeft gamma' y) :
    y ∉ rlc_twoChannelFullPhysicalVisibleRightReachSet
      gamma gamma' omega := by
  rintro ⟨x, hx, hxy⟩
  exact
    (rlc_twoChannelFullPhysical_not_visibleSourceConnector_of_failure
      omega hno) ⟨x, y, hx, hy, hxy⟩


theorem rlc_twoChannelFullPhysical_visibleSource_closed_of_crosses_reachSet
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    (source : RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma')
    {u v : RlcConnectorVertex n}
    (hsource : source.1.1 = s(u, v))
    (hcross :
      (u ∈ rlc_twoChannelFullPhysicalVisibleRightReachSet
          gamma gamma' omega ∧
        v ∉ rlc_twoChannelFullPhysicalVisibleRightReachSet
          gamma gamma' omega) ∨
      (v ∈ rlc_twoChannelFullPhysicalVisibleRightReachSet
          gamma gamma' omega ∧
        u ∉ rlc_twoChannelFullPhysicalVisibleRightReachSet
          gamma gamma' omega)) :
    omega source.1 = false := by
  have hbase : (rlc_connectorTwoChannelGraph gamma gamma').Adj u v := by
    rw [← SimpleGraph.mem_edgeSet, ← hsource]
    exact source.1.2
  obtain ⟨target, htarget⟩ := source.2
  have hvisible :
      (rlc_twoChannelFullPhysicalVisibleSourceGraph
        gamma gamma').Adj u v := by
    refine ⟨hbase, target, ?_⟩
    exact (congrArg Subtype.val htarget).trans hsource
  have hextend : rlc_twoChannelEdgeConfigExtend gamma gamma' omega
      source.1.1 = omega source.1 := by
    simp [rlc_twoChannelEdgeConfigExtend, rlc_twoChannelConfigSplitEquiv,
      source.1.2]
  cases hs : omega source.1 with
  | false => rfl
  | true =>
      exfalso
      have hopen :
          (FK.openSub
            (rlc_twoChannelFullPhysicalVisibleSourceGraph gamma gamma')
            (rlc_twoChannelEdgeConfigExtend gamma gamma' omega)).Adj u v := by
        rw [FK.openSub_adj]
        refine ⟨hvisible, ?_⟩
        rw [← hsource, hextend, hs]
      rcases hcross with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · obtain ⟨x, hx, hxu⟩ := hu
        exact hv ⟨x, hx, hxu.trans hopen.reachable⟩
      · obtain ⟨x, hx, hxv⟩ := hv
        exact hu ⟨x, hx, hxv.trans hopen.symm.reachable⟩


end
end StatMech.Universality
