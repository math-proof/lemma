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
import Instance.v1.Atlas.TensorCategories.code.SweedlerConcrete.Part2
variable {k : Type*} [Field k]


namespace SweedlerH4

/-- Componentwise formula for multiplication coefficients in `SweedlerH4 k`, in terms of the
basis structure constants. -/
@[simp] lemma coeff_mul (a b : SweedlerH4 k) (m : Fin 4) :
    (a * b).coeff m = ∑ i : Fin 4, ∑ j : Fin 4, a.coeff i * b.coeff j * basisMul i j m := rfl

/-- Componentwise formula for the unit coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_one (m : Fin 4) :
    (1 : SweedlerH4 k).coeff m = if m = 0 then 1 else 0 := rfl

/-- Componentwise formula for natural-cast coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_natCast (n : ℕ) (m : Fin 4) :
    (n : SweedlerH4 k).coeff m = if m = 0 then (n : k) else 0 := rfl

/-- Componentwise formula for integer-cast coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_intCast (n : ℤ) (m : Fin 4) :
    (n : SweedlerH4 k).coeff m = if m = 0 then (n : k) else 0 := rfl

/-- A finite sum over `Fin 4` expands as the sum of the four values at `0, 1, 2, 3`. -/
@[simp] lemma Fin4_sum (f : Fin 4 → k) :
    ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := Fin.sum_univ_four f

lemma one_mul' (a : SweedlerH4 k) : 1 * a = a := by
  ext m; simp only [coeff_mul, coeff_one, Fin4_sum, basisMul]; fin_cases m <;> simp

lemma mul_one' (a : SweedlerH4 k) : a * 1 = a := by
  ext m; simp only [coeff_mul, coeff_one, Fin4_sum, basisMul]; fin_cases m <;> simp

set_option maxHeartbeats 800000 in
lemma mul_assoc' (a b c : SweedlerH4 k) : a * b * c = a * (b * c) := by
  ext m; simp only [coeff_mul, Fin4_sum, basisMul]; fin_cases m <;> simp <;> ring

lemma left_distrib' (a b c : SweedlerH4 k) : a * (b + c) = a * b + a * c := by
  ext m; simp only [coeff_mul, coeff_add]
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]

lemma right_distrib' (a b c : SweedlerH4 k) : (a + b) * c = a * c + b * c := by
  ext m; simp only [coeff_mul, coeff_add]
  simp_rw [add_mul, Finset.sum_add_distrib]

end SweedlerH4
