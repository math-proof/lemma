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
public import Def.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part8


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

instance instDecidableIsPrincipalPrimitive (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (χ : PrimitiveCharsContaining K 𝔪 𝒞) :
    Decidable (isPrincipalPrimitive K 𝔪 𝒞 χ) := by
  unfold isPrincipalPrimitive IsRayClassCharacterPrincipal
  exact Classical.dec _

end ArtinSymbol
end
