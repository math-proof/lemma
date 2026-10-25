/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRetainedAnchoredContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWFailureSelectedCarryObstruction
import Theorem.StatisticalMechanics.Code.Universality.RSWRetainedAnchoredContour.Part3
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def rlc_windingSideCounterexample_retainedFailureAnchoredContour :
    RlcRetainedFailureAnchoredContour
      rlc_windingSideCounterexampleGap
      rlc_windingSideCounterexampleConfig where
  height := -1
  firstFace := ![-1, -1]
  secondFace := ![0, -1]
  baseFace := ![-1, -2]
  contour := rlc_traceSplitCounterexample_fullBoundaryCycle
  height_lower := by norm_num [rlc_windingSideCounterexampleGap]
  height_upper := by norm_num [rlc_windingSideCounterexampleGap]
  axis_inside := by
    rw [rlc_windingSideCounterexample_reachSet_eq,
      rlc_traceSplitCounterexample_right_vertices]
    simp
  axis_outside := by
    rw [rlc_windingSideCounterexample_reachSet_eq,
      rlc_traceSplitCounterexample_right_vertices]
    simp
  anchor_adj := rlc_traceSplitCounterexample_fullBoundary_adj12
  anchor_shared := by
    simpa using sharedPrimalEdge_right' (-1) (-1)
  contour_isCycle :=
    rlc_traceSplitCounterexample_fullBoundaryCycle_isCycle
  anchor_mem := by
    simp [rlc_traceSplitCounterexample_fullBoundaryCycle]
  carries_contact_arc :=
    rlc_traceSplitCounterexample_fullBoundaryCycle_carriesContactArc


end Universality
end StatMech
