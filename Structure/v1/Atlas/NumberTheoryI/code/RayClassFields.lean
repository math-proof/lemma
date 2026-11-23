/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
public import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
public import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
public import Def.v1.Atlas.NumberTheoryI.code.RayClassFields


public noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

structure Modulus (K : Type*) [Field K] [NumberField K] where
  toFun : Place K → ℕ
  finite_support : Set.Finite {v | toFun v ≠ 0}
  inf_le_one : ∀ v : NumberField.InfinitePlace K, toFun (Place.infinite v) ≤ 1
  complex_zero : ∀ v : NumberField.InfinitePlace K, v.IsComplex → toFun (Place.infinite v) = 0

end RayClassField
end
