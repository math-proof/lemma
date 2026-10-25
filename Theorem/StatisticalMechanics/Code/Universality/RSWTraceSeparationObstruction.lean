/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWTraceSeparationObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWTraceSeparation.Part3
import Def.StatisticalMechanics.Code.Universality.RSWTraceSeparationObstruction
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

theorem tsc_adj01 :
    ((hypercubicLattice 2).induce (rect 0 2 (-1) 1)).Adj
      tsc_v0 tsc_v1 := by
  simp [tsc_v0, tsc_v1, hypercubicLattice_adj]

theorem tsc_adj12 :
    ((hypercubicLattice 2).induce (rect 0 2 (-1) 1)).Adj
      tsc_v1 tsc_v2 := by
  simp [tsc_v1, tsc_v2, hypercubicLattice_adj]

theorem tsc_adj23 :
    ((hypercubicLattice 2).induce (rect 0 2 (-1) 1)).Adj
      tsc_v2 tsc_v3 := by
  simp [tsc_v2, tsc_v3, hypercubicLattice_adj]

end Universality
end StatMech
