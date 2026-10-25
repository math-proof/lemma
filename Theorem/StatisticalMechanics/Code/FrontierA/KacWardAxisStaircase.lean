/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearSeparation.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardAxisStaircase


namespace StatMech.FrontierA

open scoped Convex NNReal

open Set


theorem kwHorizontalPart_add_verticalPart (z : ℂ) :
    kwHorizontalPart z + kwVerticalPart z = z := by
  apply Complex.ext <;> simp [kwHorizontalPart, kwVerticalPart]

@[simp] theorem kwHorizontalPart_im (z : ℂ) :
    (kwHorizontalPart z).im = 0 := by
  simp [kwHorizontalPart]

@[simp] theorem kwVerticalPart_re (z : ℂ) :
    (kwVerticalPart z).re = 0 := by
  simp [kwVerticalPart]

theorem norm_kwHorizontalPart_le (z : ℂ) :
    ‖kwHorizontalPart z‖ ≤ ‖z‖ := by
  simpa only [kwHorizontalPart, Complex.norm_real, Real.norm_eq_abs] using
    Complex.abs_re_le_norm z

theorem norm_kwVerticalPart_le (z : ℂ) :
    ‖kwVerticalPart z‖ ≤ ‖z‖ := by
  rw [kwVerticalPart, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_eq_abs]
  exact Complex.abs_im_le_norm z


end StatMech.FrontierA
