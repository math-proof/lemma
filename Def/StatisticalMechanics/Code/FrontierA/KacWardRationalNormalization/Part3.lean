/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalPhaseReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part2


namespace StatMech.FrontierA

open scoped BigOperators


noncomputable def kwPositiveScaleLinearEquiv
    (s : ℝ) (hs : 0 < s) : ℂ ≃ₗ[ℝ] ℂ where
  toFun z := (s : ℂ) * z
  invFun z := ((s⁻¹ : ℝ) : ℂ) * z
  left_inv z := by
    dsimp only
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hs.ne',
      Complex.ofReal_one, one_mul]
  right_inv z := by
    dsimp only
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne',
      Complex.ofReal_one, one_mul]
  map_add' z w := mul_add _ _ _
  map_smul' r z := by
    simp only [RingHom.id_apply, Complex.real_smul]
    ring

end StatMech.FrontierA
