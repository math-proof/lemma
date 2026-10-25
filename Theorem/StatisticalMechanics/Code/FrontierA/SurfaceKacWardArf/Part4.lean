/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part4
open scoped BigOperators

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

theorem surface_arf_reconstruction_mul (g : Nat)
    (weight : SurfaceHomology g → Real) :
    (2 : Real) ^ g * surfaceUnsignedSectorSum weight =
      ∑ lambda : SurfaceSpinStructure g,
        surfaceParitySign (surfaceArfParity lambda) *
          surfaceTwistedSectorRoot weight lambda := by
  unfold surfaceUnsignedSectorSum surfaceTwistedSectorRoot
  calc
    (2 : Real) ^ g * ∑ h : SurfaceHomology g, weight h =
        ∑ h : SurfaceHomology g, (2 : Real) ^ g * weight h := by
      rw [Finset.mul_sum]
    _ = ∑ h : SurfaceHomology g,
        (∑ lambda : SurfaceSpinStructure g,
          surfaceParitySign
            (surfaceArfParity lambda + surfaceQuadraticParity lambda h)) *
            weight h := by
      apply Finset.sum_congr rfl
      intro h _
      rw [surface_arf_character_orthogonality]
    _ = ∑ h : SurfaceHomology g,
        ∑ lambda : SurfaceSpinStructure g,
          (surfaceParitySign (surfaceArfParity lambda) *
            surfaceParitySign (surfaceQuadraticParity lambda h)) * weight h := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro lambda _
      rw [surfaceParitySign_add]
    _ = ∑ lambda : SurfaceSpinStructure g,
        surfaceParitySign (surfaceArfParity lambda) *
          ∑ h : SurfaceHomology g,
            surfaceParitySign (surfaceQuadraticParity lambda h) * weight h := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro lambda _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring


theorem surface_arf_reconstruction (g : Nat)
    (weight : SurfaceHomology g → Real) :
    surfaceUnsignedSectorSum weight =
      ((2 : Real) ^ g)⁻¹ *
        ∑ lambda : SurfaceSpinStructure g,
          surfaceParitySign (surfaceArfParity lambda) *
            surfaceTwistedSectorRoot weight lambda := by
  rw [← surface_arf_reconstruction_mul]
  field_simp


end StatMech.FrontierA
