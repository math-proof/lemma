module
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusBoundaryReach
public import Theorem.StatisticalMechanics.Code.FK.TriHexSurfacePercolationClosure
public import Def.StatisticalMechanics.Code.FK.TriHexSurfacePercolationTransport
open Filter Finset MeasureTheory Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationTransport.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

theorem triHexTorusRadialSize_gt_two (n : Nat) :
    2 < triHexTorusRadialSize n := by
  simp [triHexTorusRadialSize]


end
end StatMech.FK.PeriodicPlanar
