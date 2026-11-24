module
public import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
public import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part2
open Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open Lattice


def triangularPlaneVertex : Site 2 ↪ Complex where
  toFun := triHexPlanePeriod
  inj' := triHexPlanePeriod_injective

end StatMech.FK.PeriodicPlanar
