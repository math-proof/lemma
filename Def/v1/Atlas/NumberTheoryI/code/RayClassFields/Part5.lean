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
import Theorem.v1.Atlas.NumberTheoryI.code.RayClassFields


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

def FracIdealsCoprime_subgroup (K : Type*) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Subgroup (FracIdeal K)ˣ where
  carrier := {I | ∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 → FracIdeal.IsCoprimeTo I v}
  one_mem' := fun v _ =>
    ⟨hasTrivialValuation_one v, by simpa using hasTrivialValuation_one v⟩
  mul_mem' := fun {a b} ha hb v hv =>
    let ⟨ha1, ha2⟩ := ha v hv
    let ⟨hb1, hb2⟩ := hb v hv
    ⟨hasTrivialValuation_mul ha1 hb1,
     by rw [mul_inv_rev]; exact hasTrivialValuation_mul hb2 ha2⟩
  inv_mem' := fun {a} ha v hv =>
    let ⟨h1, h2⟩ := ha v hv
    ⟨h2, by rwa [inv_inv]⟩

def FracIdealsCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Type u :=
  FracIdealsCoprime_subgroup K 𝔪

end RayClassField
end
