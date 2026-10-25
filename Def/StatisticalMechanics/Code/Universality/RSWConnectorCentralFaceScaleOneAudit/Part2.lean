/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceScaleOneAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part5
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceScaleOneAudit
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def axisReturn_walk :
    ((hypercubicLattice 2).induce (rect (-2) 0 (-1) 1)).Walk
      axisReturn_v0 axisReturn_v5 :=
  .cons axisReturn_adj01
    (.cons axisReturn_adj12
      (.cons axisReturn_adj23
        (.cons axisReturn_adj34 (.cons axisReturn_adj45 .nil))))


noncomputable def rlc_axisReturnCounterexampleLeft :
    RlcLeftDiagonalPath 1 := by
  let x : leftSide (-2) 0 (-1) 1 :=
    ⟨(axisReturn_v0 : Site 2), by
      simp [axisReturn_v0, mem_leftSide, mem_rect]⟩
  let y : rightSide (-2) 0 (-1) 1 :=
    ⟨(axisReturn_v5 : Site 2), by
      simp [axisReturn_v5, mem_rightSide, mem_rect]⟩
  let p : RlcCrossingPath (-2) 0 (-1) 1 :=
    ⟨x, y, axisReturn_walk.toPath⟩
  exact ⟨p, by simp [p, x, axisReturn_v0, rlc_lowerHalf],
    by simp [p, y, axisReturn_v5, rlc_upperHalf]⟩

end
end StatMech.Universality
