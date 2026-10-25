/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndomorphismNorm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Inductive.v1.Atlas.EllipticCurves.code.EndAlgClassification
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndAlgClassification
open scoped TensorProduct


namespace PositiveDefiniteInvolutionAlgebra

variable {A : Type*} [Ring A] [Algebra ℚ A] [PositiveDefiniteInvolutionAlgebra A]

/-- A nontrivial PD-involution algebra has no zero divisors: if `a * b = 0`
then `a = 0` or `b = 0`. Proved using positive-definiteness of the norm. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero [Nontrivial A] (a b : A) (hab : a * b = 0) :
    a = 0 ∨ b = 0 := by
  by_contra h
  push Not at h
  obtain ⟨ha, hb⟩ := h
  have hNb_ne : normMap b ≠ 0 := ne_of_gt (normMap_pos b hb)
  have h1 : a * (b * invol b) = 0 := by rw [← mul_assoc, hab, zero_mul]
  rw [normMap_spec b, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at h1
  have h2 : a = (normMap b)⁻¹ • (normMap b • a) := by rw [inv_smul_smul₀ hNb_ne]
  rw [h1, smul_zero] at h2
  exact ha h2

end PositiveDefiniteInvolutionAlgebra
