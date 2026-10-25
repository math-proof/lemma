/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRetainedAnchoredContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWFailureSelectedCarryObstruction
import Def.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_dualReflect_success_of_failureSelectedExtremalTraceTopology
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (htopology : RlcFailureSelectedExtremalTraceTopology G)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨h⟩ := htopology omega hno
  exact
    rlc_mixedWiredConnectorEvent_dualReflect_of_retainedFailureAnchoredContour
      G hn hlt omega h


theorem rlc_mixedWiredConnector_half_of_failureSelectedExtremalTraceTopology
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (htopology : RlcFailureSelectedExtremalTraceTopology G) :
    (1 : ℝ) / 2 ≤
      rba_selfDualMeasure.real (rlc_mixedWiredConnectorEvent G) := by
  apply rlc_mixedWiredConnector_half_of_dual_reflection G
  intro omega hno
  exact rlc_dualReflect_success_of_failureSelectedExtremalTraceTopology
    G hn hlt htopology omega hno


theorem rlc_traceSplitCounterexample_fullBoundary_adj01 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![-1, -2] ![-1, -1] := by
  apply (faceBoundaryGraph_adj_vert
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig) (-1) (-1) ?_).symm
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

theorem rlc_traceSplitCounterexample_fullBoundary_adj12 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![-1, -1] ![0, -1] := by
  apply (faceBoundaryGraph_adj_horiz
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig) 0 (-1) ?_).symm
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

theorem rlc_traceSplitCounterexample_fullBoundary_adj23 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![0, -1] ![1, -1] := by
  apply (faceBoundaryGraph_adj_horiz
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig) 1 (-1) ?_).symm
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

theorem rlc_traceSplitCounterexample_fullBoundary_adj34 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![1, -1] ![1, 0] := by
  apply (faceBoundaryGraph_adj_vert
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig) 1 0 ?_).symm
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

theorem rlc_traceSplitCounterexample_fullBoundary_adj45 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![1, 0] ![2, 0] := by
  apply (faceBoundaryGraph_adj_horiz
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig) 2 0 ?_).symm
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

theorem rlc_traceSplitCounterexample_fullBoundary_adj56 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![2, 0] ![2, -1] := by
  apply faceBoundaryGraph_adj_vert
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

theorem rlc_traceSplitCounterexample_fullBoundary_adj67 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![2, -1] ![2, -2] := by
  apply faceBoundaryGraph_adj_vert
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

theorem rlc_traceSplitCounterexample_fullBoundary_adj78 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![2, -2] ![1, -2] := by
  apply faceBoundaryGraph_adj_horiz
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

theorem rlc_traceSplitCounterexample_fullBoundary_adj89 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![1, -2] ![0, -2] := by
  apply faceBoundaryGraph_adj_horiz
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp

theorem rlc_traceSplitCounterexample_fullBoundary_adj90 :
    (faceBoundaryGraph (rlc_mixedWiredReachSet
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig)).Adj
        ![0, -2] ![-1, -2] := by
  apply faceBoundaryGraph_adj_horiz
  rw [rlc_windingSideCounterexample_reachSet_eq,
    rlc_traceSplitCounterexample_right_vertices]
  simp


end Universality
end StatMech
