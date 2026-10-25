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
import Instance.v1.Atlas.NumberTheoryI.code.RayClassFields.Part5


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

noncomputable def FrobeniusAutomorphism (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : FinitePlace K) : (L ≃ₐ[K] L) :=
  arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) (choosePrimeOver K L 𝔭)

noncomputable def primeAsUnitFracIdeal (K : Type u) [Field K] [NumberField K]
    (𝔭 : FinitePlace K) : (FracIdeal K)ˣ :=
  haveI : IsUnit (𝔭.asIdeal : FracIdeal K) :=
    isUnit_iff_exists_inv.mpr ⟨_, FractionalIdeal.coe_ideal_mul_inv 𝔭.asIdeal 𝔭.ne_bot⟩
  this.unit

end RayClassField
end
