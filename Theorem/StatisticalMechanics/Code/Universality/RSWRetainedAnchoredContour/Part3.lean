/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRetainedAnchoredContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWFailureSelectedCarryObstruction
import Def.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_traceSplitCounterexample_fullBoundaryCycle_isCycle :
    rlc_traceSplitCounterexample_fullBoundaryCycle.IsCycle := by
  rw [rlc_traceSplitCounterexample_fullBoundaryCycle,
    SimpleGraph.Walk.cons_isCycle_iff]
  constructor
  · rw [SimpleGraph.Walk.isPath_def]
    simp
  · simp

theorem rlc_traceSplitCounterexample_fullBoundaryCycle_carriesContactArc :
    RlcFaceBoundaryWalkCarriesRelaxedTraceArc
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig
      rlc_traceSplitCounterexample_fullBoundaryCycle := by
  refine ⟨![-1, -2], ![1, -1],
    rlc_traceSplitCounterexample_boundaryArc
      rlc_windingSideCounterexampleConfig
      rlc_windingSideCounterexample_reachSet_eq, ?_,
    rlc_traceSplitCounterexample_boundaryArc_rightContact,
    rlc_traceSplitCounterexample_boundaryArc_leftContact, ?_⟩
  · intro e he
    rw [rlc_traceSplitCounterexample_boundaryArc_edges] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      simp [rlc_traceSplitCounterexample_fullBoundaryCycle]
  · exact rlc_traceSplitCounterexample_boundaryArc_relaxed
      rlc_windingSideCounterexampleConfig
      rlc_windingSideCounterexample_reachSet_eq


end Universality
end StatMech
