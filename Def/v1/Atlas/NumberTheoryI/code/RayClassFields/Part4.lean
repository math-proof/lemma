module
public import Mathlib
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
public import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
public import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
public import Abbrev.v1.Atlas.NumberTheoryI.code.RayClassFields


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

def HasTrivialValuation (I : (FracIdeal K)ˣ) (v : FinitePlace K) : Prop :=
  ∃ x ∈ (↑I : FracIdeal K), v.valuation K x = 1

def FracIdeal.IsCoprimeTo (I : (FracIdeal K)ˣ) (v : FinitePlace K) : Prop :=
  HasTrivialValuation I v ∧ HasTrivialValuation I⁻¹ v

end RayClassField
end
