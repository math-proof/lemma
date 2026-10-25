/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part28
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ideles
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdeleNorm
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor227
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ch22NormGroup
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Prop2219
import Def.v1.Atlas.NumberTheoryI.code.Ideles.Part3
import Def.v1.Atlas.NumberTheoryI.code.IdeleNorm.Part4
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Theorem.v1.Atlas.NumberTheoryI.code.Cor227.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Chapter3.FiniteApproximation
import Theorem.v1.Atlas.NumberTheoryI.code.Ch22NormGroup.Part4
import Def.v1.Atlas.NumberTheoryI.code.Prop2219.Part2
import Instance.v1.Atlas.NumberTheoryI.code.GlobalCFT


noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

section ArtinSymbol

universe v

variable (K : Type v) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

noncomputable def toRayClassCharOfPrimitive (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (χ : PrimitiveCharsContaining K 𝔪 𝒞) : RayClassCharacter K 𝔪 := by
  classical


  by_cases h : RayGroup K 𝔪 ≤ 𝒞
  · exact χ.comp (QuotientGroup.map (RayGroup K 𝔪) 𝒞 (MonoidHom.id _) (fun _ hx => h hx))
  · exact 1

opaque orderOfVanishingPrimitive (_K : Type u) [Field _K] [NumberField _K]
    (_𝔪 : Modulus _K) (_𝒞 : Subgroup (FracIdealsCoprime _K _𝔪))
    (_χ : PrimitiveCharsContaining _K _𝔪 _𝒞) : ℕ

def isPrincipalPrimitive (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (χ : PrimitiveCharsContaining K 𝔪 𝒞) : Prop :=
  IsRayClassCharacterPrincipal K 𝔪 (toRayClassCharOfPrimitive K 𝔪 𝒞 χ)

end ArtinSymbol
end
