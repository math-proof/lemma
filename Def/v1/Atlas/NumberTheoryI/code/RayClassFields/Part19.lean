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
import Theorem.v1.Atlas.NumberTheoryI.code.RayClassFields.Part10


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

noncomputable def principalIdealMap (𝔪 : @Modulus K _ _) :
    UnitsCoprime_subgroup' K 𝔪 →* FracIdealsCoprime K 𝔪 where
  toFun α := ⟨toPrincipalIdeal (NumberField.RingOfIntegers K) K (α : Kˣ),
    toPrincipalIdeal_mem_FracIdealsCoprime 𝔪 (α : Kˣ) α.property⟩
  map_one' := by
    apply Subtype.ext
    show toPrincipalIdeal (NumberField.RingOfIntegers K) K (1 : Kˣ) = 1
    exact map_one _
  map_mul' x y := by
    apply Subtype.ext
    show toPrincipalIdeal _ K ((x : Kˣ) * (y : Kˣ)) =
      toPrincipalIdeal _ K (x : Kˣ) * toPrincipalIdeal _ K (y : Kˣ)
    exact map_mul _ _ _

end RayClassField
end
