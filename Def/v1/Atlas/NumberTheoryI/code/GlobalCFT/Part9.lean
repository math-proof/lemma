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
import Instance.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part2


noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

section ArtinSymbol

universe v

variable (K : Type v) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

def AllLValuesNonzero (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) : Prop :=
  ∀ χ : PrimitiveCharsContaining K 𝔪 𝒞,
    ¬isPrincipalPrimitive K 𝔪 𝒞 χ → orderOfVanishingPrimitive K 𝔪 𝒞 χ = 0

noncomputable def dirichletDensityCongruence (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (_h_cong : IsCongruenceSubgroup K 𝔪 𝒞) : ℚ :=
  haveI := _h_cong.finiteIndex

  (1 - (↑(∑ χ : PrimitiveCharsContaining K 𝔪 𝒞,
    if isPrincipalPrimitive K 𝔪 𝒞 χ then 0
    else orderOfVanishingPrimitive K 𝔪 𝒞 χ) : ℚ)) / (𝒞.index : ℚ)

noncomputable def dirichletDensityCoset (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (I : FracIdealsCoprime K 𝔪) : ℚ :=
  (DirichletDensity K {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
    (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
      FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk I}).getD 0

noncomputable def extensionAdmissibleModulus (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Modulus K where
  toFun _ := 0
  finite_support := by simp [Set.finite_empty]
  inf_le_one := fun _ => Nat.zero_le 1
  complex_zero := fun _ _ => rfl

noncomputable def extensionNormSubgroup (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Subgroup (FracIdealsCoprime K (extensionAdmissibleModulus K L)) :=
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq (fun _ => by simp)
  haveI : FiniteDimensional ℚ L := Module.Finite.trans K L
  haveI : NumberField L := NumberField.mk
  NormGroup K L (extensionAdmissibleModulus K L)

end ArtinSymbol
end
