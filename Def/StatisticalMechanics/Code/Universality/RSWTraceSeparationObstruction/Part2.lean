/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparationObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWTraceSeparation.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWTraceSeparationObstruction
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

def tsc_walk :
    ((hypercubicLattice 2).induce (rect 0 2 (-1) 1)).Walk
      tsc_v0 tsc_v3 :=
  .cons tsc_adj01 (.cons tsc_adj12 (.cons tsc_adj23 .nil))

noncomputable def rlc_traceSplitCounterexampleRight :
    RlcRightDiagonalPath 1 := by
  let x : leftSide 0 2 (-1) 1 :=
    ⟨(tsc_v0 : Site 2), by simp [tsc_v0, mem_leftSide, mem_rect]⟩
  let y : rightSide 0 2 (-1) 1 :=
    ⟨(tsc_v3 : Site 2), by simp [tsc_v3, mem_rightSide, mem_rect]⟩
  let p : RlcCrossingPath 0 2 (-1) 1 := ⟨x, y, tsc_walk.toPath⟩
  exact ⟨p, by simp [p, x, tsc_v0, rlc_lowerHalf],
    by simp [p, y, tsc_v3, rlc_upperHalf]⟩

noncomputable def rlc_traceSplitCounterexampleLeft :
    RlcLeftDiagonalPath 1 :=
  rlc_rot180RightPath rlc_traceSplitCounterexampleRight


end Universality
end StatMech
