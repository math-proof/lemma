/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceScaleOneAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFiniteGraph.Part5
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceScaleOneAudit
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem axisReturn_adj01 :
    ((hypercubicLattice 2).induce (rect (-2) 0 (-1) 1)).Adj
      axisReturn_v0 axisReturn_v1 := by
  simp [axisReturn_v0, axisReturn_v1, hypercubicLattice_adj]

theorem axisReturn_adj12 :
    ((hypercubicLattice 2).induce (rect (-2) 0 (-1) 1)).Adj
      axisReturn_v1 axisReturn_v2 := by
  simp [axisReturn_v1, axisReturn_v2, hypercubicLattice_adj]

theorem axisReturn_adj23 :
    ((hypercubicLattice 2).induce (rect (-2) 0 (-1) 1)).Adj
      axisReturn_v2 axisReturn_v3 := by
  simp [axisReturn_v2, axisReturn_v3, hypercubicLattice_adj]

theorem axisReturn_adj34 :
    ((hypercubicLattice 2).induce (rect (-2) 0 (-1) 1)).Adj
      axisReturn_v3 axisReturn_v4 := by
  simp [axisReturn_v3, axisReturn_v4, hypercubicLattice_adj]

theorem axisReturn_adj45 :
    ((hypercubicLattice 2).induce (rect (-2) 0 (-1) 1)).Adj
      axisReturn_v4 axisReturn_v5 := by
  simp [axisReturn_v4, axisReturn_v5, hypercubicLattice_adj]

end
end StatMech.Universality
