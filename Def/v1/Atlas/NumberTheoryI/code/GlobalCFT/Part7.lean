module
public import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part28
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Ideles
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.IdeleNorm
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Cor227
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Ch22NormGroup
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Prop2219
public import Def.v1.Atlas.NumberTheoryI.code.Ideles.Part3
public import Def.v1.Atlas.NumberTheoryI.code.IdeleNorm.Part4
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Theorem.v1.Atlas.NumberTheoryI.code.Cor227.Part2
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Chapter3.FiniteApproximation
public import Theorem.v1.Atlas.NumberTheoryI.code.Ch22NormGroup.Part4
public import Def.v1.Atlas.NumberTheoryI.code.Prop2219.Part2
public import Theorem.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

section ArtinSymbol

universe v

variable (K : Type v) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

noncomputable def conductorOfRayClassCharacter (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) : Modulus K :=
  conductorOfCongruenceSubgroup K 𝔪 (kernelCongruenceSubgroup K 𝔪 χ)
    (kernelCongruenceSubgroup_isCong K 𝔪 χ)

def IsRayClassCharacterPrincipal (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) : Prop :=
  χ = 1

noncomputable def WeberLFunction (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) : ℂ → ℂ :=
  RayClassField.WeberLFunction_ext χ

noncomputable def rayClassHolomorphicPart (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (γ : RayClassGroup K 𝔪) : ℂ → ℂ :=
  RayClassField.rayClassPartialZeta_regularPart γ

noncomputable def PrimeToFracIdealsCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝔭 : Prime' K) (h_coprime : 𝔪 (Place.finite 𝔭) = 0) :
    FracIdealsCoprime K 𝔪 := primeCoprime K 𝔪 𝔭 h_coprime

def primesInCongruenceSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) :
    Set (Prime' K) :=
  {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
    PrimeToFracIdealsCoprime K 𝔪 𝔭 h ∈ 𝒞}

noncomputable def PrimitiveCharsContaining (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) : Type u :=
  (FracIdealsCoprime K 𝔪 ⧸ 𝒞) →* ℂˣ

end ArtinSymbol
end
