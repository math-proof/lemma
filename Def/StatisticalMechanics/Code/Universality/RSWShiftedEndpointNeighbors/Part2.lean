/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpointNeighbors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWShiftedEndpoint.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWShiftedEndpointNeighbors.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


def rlc_sen_walk :
    ((hypercubicLattice 2).induce (rect 0 2 (-1) 1)).Walk
      rlc_sen_v0 rlc_sen_v3 :=
  .cons rlc_sen_adj01 (.cons rlc_sen_adj12 (.cons rlc_sen_adj23 .nil))


noncomputable def rlc_shiftedNeighborCounterexampleRight :
    RlcRightDiagonalPath 1 := by
  let x : leftSide 0 2 (-1) 1 :=
    ⟨(rlc_sen_v0 : Site 2), by simp [rlc_sen_v0, mem_leftSide, mem_rect]⟩
  let y : rightSide 0 2 (-1) 1 :=
    ⟨(rlc_sen_v3 : Site 2), by simp [rlc_sen_v3, mem_rightSide, mem_rect]⟩
  let gamma : RlcCrossingPath 0 2 (-1) 1 :=
    ⟨x, y, rlc_sen_walk.toPath⟩
  exact ⟨gamma, by simp [gamma, x, rlc_sen_v0, rlc_lowerHalf],
    by simp [gamma, y, rlc_sen_v3, rlc_upperHalf]⟩

end Universality
end StatMech
