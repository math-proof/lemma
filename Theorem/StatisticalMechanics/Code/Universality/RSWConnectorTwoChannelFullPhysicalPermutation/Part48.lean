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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part48
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_twoArcBadTerminalPlacement_of_firstBad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hbad : RlcTwoChannelFullPhysicalTwoArcFirstBadAt
      gamma gamma' omega c hx hy) :
    RlcTwoChannelFullPhysicalTwoArcBadTerminalPlacementAt
      gamma gamma' omega c hx hy := by
  obtain ⟨ur, vr, ul, vl, qr, rr, ql, rl, hurv, hulv,
      hbadR, hdecR, hbadL, hdecL, hne⟩ := hbad
  refine ⟨ur, vr, ul, vl, hbadR, ?_, hbadL, ?_, hne⟩
  · rw [hdecR, SimpleGraph.Walk.edges_append]
    simp
  · have hrev : s(ul, vl) ∈
        (rlc_complementaryContourArc c hx hy).reverse.edges := by
      rw [hdecL, SimpleGraph.Walk.edges_append]
      simp
    simpa [SimpleGraph.Walk.edges_reverse] using hrev


end
end StatMech.Universality
