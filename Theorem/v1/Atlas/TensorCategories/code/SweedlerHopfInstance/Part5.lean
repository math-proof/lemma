/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.SweedlerConcrete.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.SweedlerConcrete
import Def.v1.Atlas.TensorCategories.code.HopfAlgebraExamples.Part2
import Def.v1.Atlas.TensorCategories.code.SweedlerHopfInstance.Part4
set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]


namespace SweedlerH4

/-- Antipode value on `e 0 = 1`: `S(1) = 1`. -/
@[simp] lemma antipodeLM_e0 : antipodeLM (e 0 : SweedlerH4 k) = e 0 := by simp [antipodeLM]

/-- Antipode preserves the unit: `S(1) = 1`. -/
@[simp] lemma antipodeLM_one : antipodeLM (1 : SweedlerH4 k) = 1 := by
  rw [← e_zero_eq_one]; simp [antipodeLM]

/-- Antipode value on `e 1 = g`: `S(g) = g = g⁻¹`. -/
@[simp] lemma antipodeLM_e1 : antipodeLM (e 1 : SweedlerH4 k) = e 1 := by simp [antipodeLM]

/-- Antipode value on `e 2 = x`: `S(x) = gx`. -/
@[simp] lemma antipodeLM_e2 : antipodeLM (e 2 : SweedlerH4 k) = e 3 := by simp [antipodeLM]

/-- Antipode value on `e 3 = gx`: `S(gx) = -x`. -/
@[simp] lemma antipodeLM_e3 : antipodeLM (e 3 : SweedlerH4 k) = -(e 2) := by simp [antipodeLM]

/-- Left multiplication by `e 0 = 1` is the identity. -/
@[simp] lemma e0_mul (a : SweedlerH4 k) : e 0 * a = a := by rw [e_zero_eq_one, one_mul]

/-- Right multiplication by `e 0 = 1` is the identity. -/
@[simp] lemma mul_e0 (a : SweedlerH4 k) : a * e 0 = a := by rw [e_zero_eq_one, mul_one]

/-- Basis multiplication: `g · g = 1`. -/
lemma e1_mul_e1 : (e 1 : SweedlerH4 k) * e 1 = e 0 := by
  rw [show e 1 = (gen_g : SweedlerH4 k) from rfl, gen_g_sq, e_zero_eq_one]

/-- Basis multiplication: `g · x = gx`. -/
lemma e1_mul_e2 : (e 1 : SweedlerH4 k) * e 2 = e 3 := by
  rw [show e 1 = (gen_g : SweedlerH4 k) from rfl,
      show e 2 = (gen_x : SweedlerH4 k) from rfl]
  exact gen_g_mul_x

/-- Basis multiplication: `g · gx = x` (using `g² = 1`). -/
lemma e1_mul_e3 : (e 1 : SweedlerH4 k) * e 3 = e 2 := by
  ext m; simp only [coeff_mul, coeff_e, Fin4_sum, basisMul]; fin_cases m <;> simp

/-- Basis multiplication: `x · g = -gx`, expressing the anti-commutation `gx = -xg`. -/
lemma e2_mul_e1 : (e 2 : SweedlerH4 k) * e 1 = -(e 3) := by
  ext m; simp only [coeff_mul, coeff_e, coeff_neg, Fin4_sum, basisMul]; fin_cases m <;> simp

/-- Basis multiplication: `gx · g = -x`. -/
lemma e3_mul_e1 : (e 3 : SweedlerH4 k) * e 1 = -(e 2) := by
  ext m; simp only [coeff_mul, coeff_e, coeff_neg, Fin4_sum, basisMul]; fin_cases m <;> simp

/-- Basis multiplication: `gx · x = 0`. -/
lemma e3_mul_e2 : (e 3 : SweedlerH4 k) * e 2 = 0 := by
  ext m; simp only [coeff_mul, coeff_e, coeff_zero', Fin4_sum, basisMul]; fin_cases m <;> simp

end SweedlerH4
