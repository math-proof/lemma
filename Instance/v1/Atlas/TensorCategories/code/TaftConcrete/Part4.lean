/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean -/

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
import Mathlib.Data.Fintype.Prod
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Theorem.v1.Atlas.TensorCategories.code.TaftConcrete.Part2
variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {q : k}

set_option linter.unusedSectionVars false


namespace TaftAlgebraType

variable [Fact (q ^ n = 1)]

/-- The Taft algebra is an additive abelian group under pointwise operations on coefficients. -/
noncomputable instance : AddCommGroup (TaftAlgebraType n q k) where
  add_assoc a b c := by ext i; simp [add_assoc]
  zero_add a := by ext i; simp
  add_zero a := by ext i; simp
  add_comm a b := by ext i; simp [add_comm]
  neg_add_cancel a := by ext i; simp
  sub_eq_add_neg a b := by ext i; simp [sub_eq_add_neg]
  nsmul := fun c a => ⟨fun i => c • a.coeff i⟩
  nsmul_zero a := by ext i; simp
  nsmul_succ c a := by ext i; simp [add_mul, add_comm]
  zsmul := fun c a => ⟨fun i => c • a.coeff i⟩
  zsmul_zero' a := by ext i; simp
  zsmul_succ' c a := by ext i; simp [add_mul, add_comm]
  zsmul_neg' c a := by ext i; simp [Int.negSucc_eq]; ring

/-- The Taft algebra is a ring under the convolution multiplication and additive group
structure. -/
noncomputable instance : Ring (TaftAlgebraType n q k) where
  mul_assoc := mul_assoc'
  one_mul := one_mul'
  mul_one := mul_one'
  left_distrib := left_distrib'
  right_distrib := right_distrib'
  zero_mul a := by ext m; simp [zero_mul, Finset.sum_const_zero]
  mul_zero a := by ext m; simp [mul_zero, Finset.sum_const_zero]
  natCast_zero := by ext m; simp
  natCast_succ c := by ext m; simp; split <;> simp
  intCast_ofNat c := by ext m; simp
  intCast_negSucc c := by ext m; simp [Int.negSucc_eq]; split <;> simp

/-- `k`-module structure on the Taft algebra via pointwise scalar multiplication of
coefficients. -/
noncomputable instance : Module k (TaftAlgebraType n q k) where
  one_smul a := by ext i; simp
  mul_smul r s a := by ext i; simp [mul_assoc]
  smul_zero r := by ext i; simp
  smul_add r a b := by ext i; simp [mul_add]
  add_smul r s a := by ext i; simp [add_mul]
  zero_smul a := by ext i; simp

/-- `k`-algebra structure on the Taft algebra, derived from the module and ring structures via
`Algebra.ofModule`. -/
noncomputable instance : Algebra k (TaftAlgebraType n q k) :=
  Algebra.ofModule
    (fun r x y => by
      ext m; simp only [coeff_smul, coeff_mul]
      rw [Finset.mul_sum]; congr 1; ext i
      rw [Finset.mul_sum]; congr 1; ext j; ring)
    (fun r x y => by
      ext m; simp only [coeff_smul, coeff_mul]
      rw [Finset.mul_sum]; congr 1; ext i
      rw [Finset.mul_sum]; congr 1; ext j; ring)

end TaftAlgebraType
