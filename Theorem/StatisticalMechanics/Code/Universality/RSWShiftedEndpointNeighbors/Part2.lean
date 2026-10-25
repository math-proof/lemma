/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWShiftedEndpointNeighbors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWShiftedEndpoint.Part3
import Def.StatisticalMechanics.Code.Universality.RSWShiftedEndpointNeighbors
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_sen_adj01 :
    ((hypercubicLattice 2).induce (rect 0 2 (-1) 1)).Adj
      rlc_sen_v0 rlc_sen_v1 := by
  simp [rlc_sen_v0, rlc_sen_v1, hypercubicLattice_adj]

theorem rlc_sen_adj12 :
    ((hypercubicLattice 2).induce (rect 0 2 (-1) 1)).Adj
      rlc_sen_v1 rlc_sen_v2 := by
  simp [rlc_sen_v1, rlc_sen_v2, hypercubicLattice_adj]

theorem rlc_sen_adj23 :
    ((hypercubicLattice 2).induce (rect 0 2 (-1) 1)).Adj
      rlc_sen_v2 rlc_sen_v3 := by
  simp [rlc_sen_v2, rlc_sen_v3, hypercubicLattice_adj]

end Universality
end StatMech
