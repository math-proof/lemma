/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22WeberLFunction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part28
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
import Abbrev.v1.Atlas.NumberTheoryI.code.Ch22WeberLFunction


noncomputable section

open scoped NumberField

namespace RayClassField

universe u

def toRayClass (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : FracIdealsCoprime K 𝔪 →* RayClassGroup K 𝔪 :=
  QuotientGroup.mk' (RayGroup K 𝔪)

def primeToFracIdealsCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝔭 : Prime' K) (h : 𝔪 (Place.finite 𝔭) = 0) :
    FracIdealsCoprime K 𝔪 :=
  primeCoprime K 𝔪 𝔭 h

def RayClassChar.evalIdeal {K : Type u} [Field K] [NumberField K]
    {𝔪 : Modulus K} (χ : RayClassChar K 𝔪)
    (𝔞 : FracIdealsCoprime K 𝔪) : ℂˣ :=
  χ (toRayClass K 𝔪 𝔞)

def RayClassChar.evalIdealC {K : Type u} [Field K] [NumberField K]
    {𝔪 : Modulus K} (χ : RayClassChar K 𝔪)
    (𝔞 : FracIdealsCoprime K 𝔪) : ℂ :=
  (χ.evalIdeal 𝔞 : ℂ)

def RayClassChar.evalPrime {K : Type u} [Field K] [NumberField K]
    {𝔪 : Modulus K} (χ : RayClassChar K 𝔪)
    (𝔭 : Prime' K) : ℂ := by
  classical
  exact if h : 𝔪 (Place.finite 𝔭) = 0 then
    (χ.evalIdeal (primeToFracIdealsCoprime K 𝔪 𝔭 h) : ℂ)
  else
    0

def RayClassChar.IsPrincipal {K : Type u} [Field K] [NumberField K]
    {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) : Prop :=
  ∀ g : RayClassGroup K 𝔪, χ g = 1

def weberEulerFactor {K : Type u} [Field K] [NumberField K]
    {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) (𝔭 : Prime' K) (s : ℂ) : ℂ :=
  (1 - χ.evalPrime 𝔭 * (↑(Ideal.absNorm 𝔭.asIdeal) : ℂ) ^ (-s))⁻¹

def WeberLFunction (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassChar K 𝔪) (s : ℂ) : ℂ :=
  ∏' (𝔭 : Prime' K), weberEulerFactor χ 𝔭 s

end RayClassField
end
