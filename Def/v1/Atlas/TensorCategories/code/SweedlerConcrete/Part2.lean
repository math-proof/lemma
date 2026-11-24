module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Instance.v1.Atlas.TensorCategories.code.SweedlerConcrete.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {k : Type*} [Field k]


namespace SweedlerH4

/-- The canonical `k`-linear equivalence between `SweedlerH4 k` and `Fin 4 → k` extracting the
coefficient tuple. -/
noncomputable def toFunEquiv : SweedlerH4 k ≃ₗ[k] (Fin 4 → k) where
  toFun a := a.coeff
  invFun f := ⟨f⟩
  map_add' a b := rfl
  map_smul' r a := by ext i; simp [Pi.smul_apply, smul_eq_mul]
  left_inv a := rfl
  right_inv f := rfl

end SweedlerH4
