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
import Theorem.v1.Atlas.NumberTheoryI.code.RayClassFields.Part13


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

noncomputable def signMapHom (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    UnitsCoprime_subgroup' K 𝔪 →*
      (𝔪.infSupportFinset → Multiplicative (ZMod 2)) where
  toFun α := fun ⟨w, hw⟩ =>
    Multiplicative.ofAdd (signAtPlace (𝔪.infSupportFinset_isReal hw) (α : Kˣ))
  map_one' := by
    funext ⟨w, hw⟩
    simp only [Pi.one_apply, signAtPlace]
    norm_num
  map_mul' a b := by
    funext ⟨w, hw⟩
    simp only [Pi.mul_apply]
    show Multiplicative.ofAdd (signAtPlace _ ((a * b : UnitsCoprime_subgroup' K 𝔪) : Kˣ)) =
      Multiplicative.ofAdd (signAtPlace _ (a : Kˣ)) *
      Multiplicative.ofAdd (signAtPlace _ (b : Kˣ))
    have hab : ((a * b : UnitsCoprime_subgroup' K 𝔪) : Kˣ) = (a : Kˣ) * (b : Kˣ) := by
      simp [Subgroup.coe_mul]
    rw [hab, signAtPlace_mul, ofAdd_add]

end RayClassField
end
