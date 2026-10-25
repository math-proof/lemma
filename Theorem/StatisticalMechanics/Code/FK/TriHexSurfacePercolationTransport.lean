/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusBoundaryReach
import Theorem.StatisticalMechanics.Code.FK.TriHexSurfacePercolationClosure
import Def.StatisticalMechanics.Code.FK.TriHexSurfacePercolationTransport
open Filter Finset MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

theorem triHexTorusRadialSize_gt_two (n : Nat) :
    2 < triHexTorusRadialSize n := by
  simp [triHexTorusRadialSize]


end
end StatMech.FK.PeriodicPlanar
