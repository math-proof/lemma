/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part6
open Set


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem hexagonalPlaneVertexValue_injective :
    Function.Injective hexagonalPlaneVertexValue := by
  rintro ⟨x, xb⟩ ⟨y, yb⟩ h
  cases xb <;> cases yb
  · apply Prod.ext
    · apply triHexPlanePeriod_injective
      exact add_right_cancel h
    · rfl
  · have hre := congrArg Complex.re h
    simp [hexagonalPlaneVertexValue, hexagonalFaceCenterOffset] at hre
    have hre' : (3 : Real) * (x 0 : Real) + 1 =
        (3 : Real) * (y 0 : Real) - 1 := by
      linarith
    have hreInt : (3 : Int) * x 0 + 1 = (3 : Int) * y 0 - 1 := by
      exact_mod_cast hre'
    omega
  · have hre := congrArg Complex.re h
    simp [hexagonalPlaneVertexValue, hexagonalFaceCenterOffset] at hre
    have hre' : (3 : Real) * (x 0 : Real) - 1 =
        (3 : Real) * (y 0 : Real) + 1 := by
      linarith
    have hreInt : (3 : Int) * x 0 - 1 = (3 : Int) * y 0 + 1 := by
      exact_mod_cast hre'
    omega
  · apply Prod.ext
    · apply triHexPlanePeriod_injective
      exact add_right_cancel h
    · rfl


end StatMech.FK.PeriodicPlanar
