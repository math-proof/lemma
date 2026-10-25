/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor227.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.NumberTheoryI.code.Prop226
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Prop226


noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

lemma Modulus.dvd_antisymm' {𝔪₁ 𝔪₂ : Modulus K} (h₁ : 𝔪₁.dvd 𝔪₂) (h₂ : 𝔪₂.dvd 𝔪₁) :
    𝔪₁ = 𝔪₂ := by
  have : ∀ v, 𝔪₁ v = 𝔪₂ v := fun v => le_antisymm (h₁ v) (h₂ v)
  cases 𝔪₁; cases 𝔪₂
  congr 1
  funext v
  exact this v

end RayClassField
end
