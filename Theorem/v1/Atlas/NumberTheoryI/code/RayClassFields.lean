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
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part4


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

lemma hasTrivialValuation_one (v : FinitePlace K) :
    HasTrivialValuation (1 : (FracIdeal K)ˣ) v :=
  ⟨1, by rw [Units.val_one]; exact FractionalIdeal.one_mem_one _, Valuation.map_one _⟩

lemma hasTrivialValuation_mul {a b : (FracIdeal K)ˣ} {v : FinitePlace K}
    (ha : HasTrivialValuation a v) (hb : HasTrivialValuation b v) :
    HasTrivialValuation (a * b) v := by
  obtain ⟨x, hx, hvx⟩ := ha
  obtain ⟨y, hy, hvy⟩ := hb
  exact ⟨x * y, by rw [Units.val_mul]; exact FractionalIdeal.mul_mem_mul hx hy,
    by simp [map_mul, hvx, hvy]⟩

end RayClassField
end
