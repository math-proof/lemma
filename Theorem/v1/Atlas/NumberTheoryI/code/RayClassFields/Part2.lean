/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
import Instance.v1.Atlas.NumberTheoryI.code.RayClassFields.Part4


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

lemma choosePrimeOver_over (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : FinitePlace K) :
    (choosePrimeOver K L 𝔭).comap
      (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) = 𝔭.asIdeal :=
  (Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) 𝔭.asIdeal ⊥ (by simp)).choose_spec.2.2

lemma choosePrimeOver_ne_bot (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : FinitePlace K) :
    choosePrimeOver K L 𝔭 ≠ ⊥ := by
  intro h
  have hcomap := choosePrimeOver_over K L 𝔭
  rw [h, Ideal.comap_bot_of_injective] at hcomap
  · exact 𝔭.ne_bot hcomap.symm
  · exact FaithfulSMul.algebraMap_injective _ _

end RayClassField
end
