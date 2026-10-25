/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAxisStaircase.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardGenericShear


namespace StatMech.FrontierA

@[simp] theorem kwShearX_re (t : ℝ) (z : ℂ) :
    (kwShearX t z).re = z.re + t * z.im := by
  simp [kwShearX]

@[simp] theorem kwShearX_im (t : ℝ) (z : ℂ) :
    (kwShearX t z).im = z.im := by
  simp [kwShearX]

@[simp] theorem kwShearY_re (t : ℝ) (z : ℂ) :
    (kwShearY t z).re = z.re := by
  simp [kwShearY]

@[simp] theorem kwShearY_im (t : ℝ) (z : ℂ) :
    (kwShearY t z).im = z.im + t * z.re := by
  simp [kwShearY]

theorem kwComplexCross_shearX (t : ℝ) (z w : ℂ) :
    kwComplexCross (kwShearX t z) (kwShearX t w) =
      kwComplexCross z w := by
  unfold kwComplexCross
  simp only [kwShearX_re, kwShearX_im]
  ring

theorem kwComplexCross_shearY (t : ℝ) (z w : ℂ) :
    kwComplexCross (kwShearY t z) (kwShearY t w) =
      kwComplexCross z w := by
  unfold kwComplexCross
  simp only [kwShearY_re, kwShearY_im]
  ring

end StatMech.FrontierA
