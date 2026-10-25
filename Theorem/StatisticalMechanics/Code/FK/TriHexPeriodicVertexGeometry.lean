/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry
open Set


namespace StatMech.FK.PeriodicPlanar

open Lattice


@[simp] theorem triHexPlanePeriod_re (z : Site 2) :
    (triHexPlanePeriod z).re = z 0 := by
  simp [triHexPlanePeriod]

@[simp] theorem triHexPlanePeriod_im (z : Site 2) :
    (triHexPlanePeriod z).im = z 1 := by
  simp [triHexPlanePeriod]

theorem triHexPlanePeriod_injective :
    Function.Injective triHexPlanePeriod := by
  intro z w h
  funext i
  fin_cases i
  · have hreal : (z 0 : Real) = (w 0 : Real) := by
      simpa using congrArg Complex.re h
    exact_mod_cast hreal
  · have himag : (z 1 : Real) = (w 1 : Real) := by
      simpa using congrArg Complex.im h
    exact_mod_cast himag


end StatMech.FK.PeriodicPlanar
