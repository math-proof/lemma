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
import Theorem.v1.Atlas.TensorCategories.code.SweedlerConcrete.Part2
variable {k : Type*} [Field k]


namespace SweedlerH4

/-- `SweedlerH4 k` is an additive abelian group under componentwise operations. -/
noncomputable instance : AddCommGroup (SweedlerH4 k) where
  add_assoc a b c := by ext i; simp [add_assoc]
  zero_add a := by ext i; simp
  add_zero a := by ext i; simp
  add_comm a b := by ext i; simp [add_comm]
  neg_add_cancel a := by ext i; simp
  sub_eq_add_neg a b := by ext i; simp [sub_eq_add_neg]
  nsmul := fun n a => ⟨fun i => n • a.coeff i⟩
  nsmul_zero a := by ext i; simp
  nsmul_succ n a := by ext i; simp [add_mul, add_comm]
  zsmul := fun n a => ⟨fun i => n • a.coeff i⟩
  zsmul_zero' a := by ext i; simp
  zsmul_succ' n a := by ext i; simp [add_mul, add_comm]
  zsmul_neg' n a := by ext i; simp [Int.negSucc_eq]; ring

/-- `SweedlerH4 k` is a (noncommutative) ring with multiplication given by the basis structure
constants `basisMul`. -/
noncomputable instance : Ring (SweedlerH4 k) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  zero_mul a := by ext m; simp [zero_mul, Finset.sum_const_zero]
  mul_zero a := by ext m; simp [mul_zero, Finset.sum_const_zero]
  natCast_zero := by ext m; simp
  natCast_succ n := by ext m; simp; split <;> simp
  intCast_ofNat n := by ext m; simp
  intCast_negSucc n := by ext m; simp [Int.negSucc_eq]; split <;> simp

/-- `SweedlerH4 k` is a `k`-module under componentwise scaling. -/
noncomputable instance : Module k (SweedlerH4 k) where
  one_smul a := by ext i; simp
  mul_smul r s a := by ext i; simp [mul_assoc]
  smul_zero r := by ext i; simp
  smul_add r a b := by ext i; simp [mul_add]
  add_smul r s a := by ext i; simp [add_mul]
  zero_smul a := by ext i; simp

/-- `SweedlerH4 k` is a `k`-algebra with scalar action factoring through multiplication by `e₀`. -/
noncomputable instance : Algebra k (SweedlerH4 k) :=
  Algebra.ofModule
    (fun r x y => by
      ext m; simp only [coeff_smul, coeff_mul]
      rw [Finset.mul_sum]; congr 1; ext i
      rw [Finset.mul_sum]; congr 1; ext j; ring)
    (fun r x y => by
      ext m; simp only [coeff_smul, coeff_mul]
      rw [Finset.mul_sum]; congr 1; ext i
      rw [Finset.mul_sum]; congr 1; ext j; ring)

end SweedlerH4
