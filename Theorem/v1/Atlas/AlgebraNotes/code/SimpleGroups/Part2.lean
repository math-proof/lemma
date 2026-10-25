/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SimpleGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraNotes.code.SimpleGroups.Part3


namespace SimpleGroups

open Matrix

section OneParamSubgroupTheorem

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma diagRotation_periodic (θ : ℝ) (n : ℤ) :
    diagRotation (θ + n * (2 * Real.pi)) = diagRotation θ := by
  simp only [diagRotation]
  ext i j; fin_cases i <;> fin_cases j <;> simp
  · have h : (↑θ + ↑n * (2 * (↑Real.pi : ℂ))) * Complex.I =
        ↑θ * Complex.I + ↑n * (2 * ↑Real.pi * Complex.I) := by ring
    rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · have h : -((↑θ + ↑n * (2 * (↑Real.pi : ℂ))) * Complex.I) =
        -(↑θ * Complex.I) + (-(↑n : ℂ)) * (2 * ↑Real.pi * Complex.I) := by ring
    rw [h, Complex.exp_add]
    rw [show -(↑n : ℂ) * (2 * ↑Real.pi * Complex.I) = ↑(-n) * (2 * ↑Real.pi * Complex.I) from by push_cast; ring]
    rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]

end OneParamSubgroupTheorem
end SimpleGroups
