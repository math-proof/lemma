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
import Instance.v1.Atlas.NumberTheoryI.code.RayClassFields.Part6


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

def Modulus.infSupportFinset (𝔪 : @Modulus K _ _) :
    Finset (NumberField.InfinitePlace K) :=
  (𝔪.finite_support.preimage (f := Place.infinite)
    (fun a _ b _ hab => by cases hab; rfl)).toFinset

def UnitsCoprime_subgroup' (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Subgroup Kˣ where
  carrier := {α | ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
    v.valuation K (α : K) = 1}
  one_mem' := fun v _ => Valuation.map_one _
  mul_mem' := fun {a b} ha hb v hv => by simp [map_mul, ha v hv, hb v hv]
  inv_mem' := fun {a} ha v hv => by simp [map_inv₀, ha v hv]

def UnitsCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Type u :=
  UnitsCoprime_subgroup' K 𝔪

end RayClassField
end
