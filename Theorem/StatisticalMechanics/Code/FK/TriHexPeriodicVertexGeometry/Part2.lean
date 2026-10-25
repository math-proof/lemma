/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part2
open Set


namespace StatMech.FK.PeriodicPlanar

open Lattice


@[simp] theorem triHexPlaneCoordinates_apply_zero (z : Complex) :
    triHexPlaneCoordinates z 0 = z.re := by
  rfl

@[simp] theorem triHexPlaneCoordinates_apply_one (z : Complex) :
    triHexPlaneCoordinates z 1 = z.im := by
  rfl

@[simp] theorem triHexPlaneCoordinates_period
    (z : Site 2) (i : Fin 2) :
    triHexPlaneCoordinates (triHexPlanePeriod z) i = z i := by
  fin_cases i <;> simp


end StatMech.FK.PeriodicPlanar
