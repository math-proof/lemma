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
import Structure.v1.Atlas.NumberTheoryI.code.RayClassFields.Part3


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

lemma choosePrimeOver_comap_ne_bot
    (K : Type u) (L : Type u) (M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsGalois K L] [IsGalois K M]
    [IsScalarTower K L M]
    (𝔭 : FinitePlace K) :
    (choosePrimeOver K M 𝔭).comap
      (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M)) ≠ ⊥ := by
  intro h
  have hunder := choosePrimeOver_over K M 𝔭
  have : ((choosePrimeOver K M 𝔭).comap
      (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))).comap
      (algebraMap (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)) = 𝔭.asIdeal := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]; exact hunder
  rw [h, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)] at this
  exact 𝔭.ne_bot this.symm

end RayClassField
end
