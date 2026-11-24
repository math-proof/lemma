module
public import Mathlib
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
public import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
public import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
public import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part7


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

instance choosePrimeOver_isPrime (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : FinitePlace K) :
    (choosePrimeOver K L 𝔭).IsPrime :=
  (Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) 𝔭.asIdeal ⊥ (by simp)).choose_spec.2.1

end RayClassField
end
