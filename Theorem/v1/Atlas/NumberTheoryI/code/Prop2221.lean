/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2221.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.NumberTheoryI.code.Theorem2220
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Theorem2220

public section

noncomputable section

open NumberField RayClassField GlobalCFT

namespace CosetDensity

universe u

variable (K : Type u) [Field K] [NumberField K]
  (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)

end CosetDensity
end
