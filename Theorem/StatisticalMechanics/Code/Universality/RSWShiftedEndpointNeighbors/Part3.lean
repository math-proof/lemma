/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpointNeighbors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWShiftedEndpoint.Part3
import Def.StatisticalMechanics.Code.Universality.RSWShiftedEndpointNeighbors.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


@[simp] theorem rlc_shiftedNeighborCounterexampleRight_start_one :
    (rlc_shiftedNeighborCounterexampleRight.1.1 : Site 2) 1 = -1 := by
  simp [rlc_shiftedNeighborCounterexampleRight, rlc_sen_v0]


theorem rlc_shiftedEndpointTraceNeighbors_counterexample :
    ¬ RlcShiftedEndpointTraceNeighbors
      rlc_shiftedNeighborCounterexampleRight
      (rlc_rot180RightPath rlc_shiftedNeighborCounterexampleRight) := by
  apply rlc_not_shiftedEndpointTraceNeighbors_of_right_start_bottom
  exact rlc_shiftedNeighborCounterexampleRight_start_one

end Universality
end StatMech
