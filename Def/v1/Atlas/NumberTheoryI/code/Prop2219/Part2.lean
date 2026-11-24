module
public import Instance.v1.Atlas.NumberTheoryI.code.Ch22WeberLFunction
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Ch22WeberLFunction
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.AnalyticClassNumber
public import Instance.v1.Atlas.NumberTheoryI.code.AnalyticClassNumber.Part3
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Cor1838
public import Structure.v1.Atlas.NumberTheoryI.code.Prop2219


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped NumberField

open Complex Finset Section19

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

def WeberLFunction_ext {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) (s : ℂ) : ℂ :=
  ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) * rayClassPartialZeta_ext γ s

end RayClassField
end
