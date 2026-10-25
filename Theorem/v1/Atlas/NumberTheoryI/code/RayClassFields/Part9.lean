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
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part17


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

lemma valuation_algebraMap_unit_eq_one
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : (NumberField.RingOfIntegers K)ˣ) :
    v.valuation K (algebraMap (NumberField.RingOfIntegers K) K u.val) = 1 := by
  have h1 : v.valuation K (algebraMap _ K u.val) ≤ 1 := v.valuation_le_one u.val
  have h2 : v.valuation K (algebraMap _ K u.inv) ≤ 1 := v.valuation_le_one u.inv
  have h3 : v.valuation K (algebraMap _ K u.val) *
             v.valuation K (algebraMap _ K u.inv) = 1 := by
    rw [← map_mul (v.valuation K), ← map_mul (algebraMap _ K), u.val_inv, map_one, map_one]
  exact le_antisymm h1 (by
    calc (1 : WithZero (Multiplicative ℤ))
        = v.valuation K (algebraMap _ K u.val) *
          v.valuation K (algebraMap _ K u.inv) := h3.symm
      _ ≤ v.valuation K (algebraMap _ K u.val) * 1 := by gcongr
      _ = v.valuation K (algebraMap _ K u.val) := mul_one _)

theorem okUnitsInUnitsCoprime (𝔪 : @Modulus K _ _)
    (u : (NumberField.RingOfIntegers K)ˣ) :
    okUnitsToKUnits u ∈ UnitsCoprime_subgroup' K 𝔪 := by
  intro v _
  exact valuation_algebraMap_unit_eq_one v u

end RayClassField
end
