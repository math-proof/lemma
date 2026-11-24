module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Fintype.Prod
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Instance.v1.Atlas.TensorCategories.code.TaftConcrete.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {q : k}

set_option linter.unusedSectionVars false


namespace TaftAlgebraType

variable [Fact (q ^ n = 1)]

/-- `k`-linear equivalence between `TaftAlgebraType n q k` and `Fin n × Fin n → k`. -/
noncomputable def toFunEquiv : TaftAlgebraType n q k ≃ₗ[k] (Fin n × Fin n → k) where
  toFun a := a.coeff
  invFun f := ⟨f⟩
  map_add' a b := rfl
  map_smul' r a := by ext i; simp [Pi.smul_apply, smul_eq_mul]
  left_inv a := rfl
  right_inv f := rfl

end TaftAlgebraType
