/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Def.v1.Atlas.TensorCategories.code.SweedlerConcrete.Part3
variable {k : Type*} [Field k]


namespace SweedlerH4

/-- Coefficient formula for the basis vector `e i`. -/
@[simp] lemma coeff_e (i j : Fin 4) :
    (e i : SweedlerH4 k).coeff j = if i = j then 1 else 0 := rfl

/-- Coefficient formula for the generator `g = e 1`. -/
@[simp] lemma coeff_gen_g (j : Fin 4) :
    (gen_g : SweedlerH4 k).coeff j = if (1 : Fin 4) = j then 1 else 0 := rfl

/-- Coefficient formula for the generator `x = e 2`. -/
@[simp] lemma coeff_gen_x (j : Fin 4) :
    (gen_x : SweedlerH4 k).coeff j = if (2 : Fin 4) = j then 1 else 0 := rfl

/-- Defining anti-commutation relation of `H₄`: `gx = -xg`. -/
lemma gen_gx_comm : (gen_g : SweedlerH4 k) * gen_x = -(gen_x * gen_g) := by
  ext m; simp only [gen_g, gen_x, coeff_mul, coeff_e, coeff_neg, Fin4_sum, basisMul]
  fin_cases m <;> simp

/-- The product `g · x` is the fourth basis vector `e 3`, i.e. the basis element usually denoted
`gx`. -/
lemma gen_g_mul_x : (gen_g : SweedlerH4 k) * gen_x = e 3 := by
  ext m; simp only [gen_g, gen_x, coeff_mul, coeff_e, Fin4_sum, basisMul]
  fin_cases m <;> simp

/-- The first basis vector `e 0` is the multiplicative unit `1` of `SweedlerH4 k`. -/
lemma e_zero_eq_one : (e 0 : SweedlerH4 k) = 1 := by
  ext m; simp only [coeff_e, coeff_one, eq_comm]

end SweedlerH4
