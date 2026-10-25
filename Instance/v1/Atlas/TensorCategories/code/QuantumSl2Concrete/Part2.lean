/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean -/

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
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Def.v1.Atlas.TensorCategories.code.QuantumSl2.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.QuantumSl2
import Theorem.v1.Atlas.TensorCategories.code.QuantumSl2Concrete
variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

/-- Componentwise additive abelian group structure. -/
noncomputable instance : AddCommGroup (SmallQuantumSl2 n k) where
  add_assoc a b c := by ext i; simp [add_assoc]
  zero_add a := by ext i; simp
  add_zero a := by ext i; simp
  add_comm a b := by ext i; simp [add_comm]
  neg_add_cancel a := by ext i; simp
  sub_eq_add_neg a b := by ext i; simp [sub_eq_add_neg]
  nsmul := fun m a => ⟨fun i => m • a.coeff i⟩
  nsmul_zero a := by ext i; simp
  nsmul_succ m a := by ext i; simp [add_mul, add_comm]
  zsmul := fun m a => ⟨fun i => m • a.coeff i⟩
  zsmul_zero' a := by ext i; simp
  zsmul_succ' m a := by ext i; simp [add_mul, add_comm]
  zsmul_neg' m a := by ext i; simp [Int.negSucc_eq]; ring

/-- Componentwise `k`-module structure. -/
noncomputable instance : Module k (SmallQuantumSl2 n k) where
  one_smul a := by ext i; simp
  mul_smul r s a := by ext i; simp [mul_assoc]
  smul_zero r := by ext i; simp
  smul_add r a b := by ext i; simp [mul_add]
  add_smul r s a := by ext i; simp [add_mul]
  zero_smul a := by ext i; simp

end SmallQuantumSl2
