module
public import Mathlib
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
public import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
public import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
public import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part18


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

attribute [instance] instFintypeSignsTimesUnits

lemma toPrincipalIdeal_mem_FracIdealsCoprime (𝔪 : @Modulus K _ _)
    (α : Kˣ) (hα : α ∈ UnitsCoprime_subgroup' K 𝔪) :
    toPrincipalIdeal (NumberField.RingOfIntegers K) K α ∈
      FracIdealsCoprime_subgroup K 𝔪 := by
  intro v hv
  constructor
  ·
    refine ⟨(α : K), ?_, hα v hv⟩
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  ·
    refine ⟨((α⁻¹ : Kˣ) : K), ?_, ?_⟩
    · rw [← MonoidHom.map_inv, coe_toPrincipalIdeal]
      exact FractionalIdeal.mem_spanSingleton_self _ _
    · have := (UnitsCoprime_subgroup' K 𝔪).inv_mem hα v hv
      exact this

end RayClassField
end
