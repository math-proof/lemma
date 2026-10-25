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
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part19


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

lemma principalIdealMap_val (𝔪 : @Modulus K _ _)
    (α : UnitsCoprime_subgroup' K 𝔪) :
    ((principalIdealMap 𝔪 α).val : (FracIdeal K)ˣ).val =
      FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers K)) ((α : Kˣ) : K) := by
  show (toPrincipalIdeal (NumberField.RingOfIntegers K) K (α : Kˣ) : FracIdeal K) = _
  exact coe_toPrincipalIdeal _

theorem principalIdealMap_congruent_to_ray (𝔪 : @Modulus K _ _)
    (α : UnitsCoprime_subgroup' K 𝔪)
    (hα : (α : Kˣ) ∈ UnitsCongruent_subgroup' K 𝔪) :
    principalIdealMap 𝔪 α ∈ RayGroup K 𝔪 := by


  apply Subgroup.subset_closure

  show IsRayGenerator 𝔪 (principalIdealMap 𝔪 α)
  refine ⟨(α : Kˣ), ?_, ?_, ?_⟩
  ·
    exact principalIdealMap_val 𝔪 α
  ·
    exact hα.2.1
  ·
    exact hα.2.2

end RayClassField
end
