/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Theorem2220.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.NumberTheoryI.code.GlobalCFT
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GlobalCFT

noncomputable section

open NumberField RayClassField GlobalCFT

namespace DirichletDensity

universe u

variable (K : Type u) [Field K] [NumberField K]
  (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)

def sumOrdersNonprincipal (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (_h_cong : IsCongruenceSubgroup K 𝔪 𝒞) : ℕ :=
  haveI := _h_cong.finiteIndex
  ∑ χ : PrimitiveCharsContaining K 𝔪 𝒞,
    if GlobalCFT.isPrincipalPrimitive K 𝔪 𝒞 χ then 0
    else GlobalCFT.orderOfVanishingPrimitive K 𝔪 𝒞 χ
