/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop226.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.Lem225
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Lem225


noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

lemma Modulus.dvd_lcm_left (𝔪₁ 𝔪₂ : Modulus K) : 𝔪₁.dvd (𝔪₁.lcm 𝔪₂) :=
  fun _ => le_max_left _ _

lemma Modulus.dvd_lcm_right (𝔪₁ 𝔪₂ : Modulus K) : 𝔪₂.dvd (𝔪₁.lcm 𝔪₂) :=
  fun _ => le_max_right _ _

end RayClassField
end
