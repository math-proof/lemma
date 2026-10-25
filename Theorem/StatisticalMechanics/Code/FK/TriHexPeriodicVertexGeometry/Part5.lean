/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicVertexGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDualShift.Part3
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicVertexGeometry.Part5
open Set


namespace StatMech.FK.PeriodicPlanar

open Lattice


@[simp] theorem hexagonalFaceCenterOffset_false :
    hexagonalFaceCenterOffset false =
      (1 / 3 : Real) + (1 / 3 : Real) * Complex.I := rfl

@[simp] theorem hexagonalFaceCenterOffset_true :
    hexagonalFaceCenterOffset true =
      -(1 / 3 : Real) - (1 / 3 : Real) * Complex.I := rfl

theorem hexagonalFaceCenterOffset_norm_le_one (white : Bool) :
    ‖hexagonalFaceCenterOffset white‖ <= 1 := by
  cases white
  · calc
      ‖hexagonalFaceCenterOffset false‖ <=
          ‖((1 / 3 : Real) : Complex)‖ +
            ‖((1 / 3 : Real) : Complex) * Complex.I‖ := by
        simpa [hexagonalFaceCenterOffset] using
          norm_add_le ((1 / 3 : Real) : Complex)
            (((1 / 3 : Real) : Complex) * Complex.I)
      _ <= 1 := by norm_num [norm_mul]
  · calc
      ‖hexagonalFaceCenterOffset true‖ <=
          ‖(-((1 / 3 : Real) : Complex))‖ +
            ‖((1 / 3 : Real) : Complex) * Complex.I‖ := by
        simpa [hexagonalFaceCenterOffset] using
          norm_sub_le (-((1 / 3 : Real) : Complex))
            (((1 / 3 : Real) : Complex) * Complex.I)
      _ <= 1 := by norm_num [norm_mul]


end StatMech.FK.PeriodicPlanar
