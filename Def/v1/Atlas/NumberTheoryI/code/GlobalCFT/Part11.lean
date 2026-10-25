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
import Theorem.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part7


noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

open Ideles

attribute [instance] GlobalArtinMap.instPreorder
  GlobalArtinMap.instFintype
  GlobalArtinMap.instCommGroup
  GlobalArtinMap.galAb_group
  GlobalArtinMap.galAb_topologicalSpace
  GlobalArtinMap.galAb_topologicalGroup
  GlobalArtinMap.galAb_compactSpace

noncomputable def GlobalArtinMap.artinHomCK {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) :
    IdeleClassGroup K →* θ.GalAb :=
  QuotientGroup.lift (principalIdeles K) θ.artinHom (theorem_28_4_principal_in_ker θ)

noncomputable def GlobalArtinMap.normSubgroupCK {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (i : θ.I) :
    Subgroup (IdeleClassGroup K) :=
  θ.normSubgroup i

noncomputable def GlobalArtinMap.artinMapCK {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (i : θ.I) :
    IdeleClassGroup K →* θ.GalLK i :=
  (θ.proj i).comp θ.artinHomCK

def IsConjugationStable {G : Type*} [Group G] (C : Set G) : Prop :=
  ∀ g : G, ∀ c ∈ C, g * c * g⁻¹ ∈ C

noncomputable def FrobeniusConjClass (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (𝔭 : Prime' K) : Set (L ≃ₐ[K] L) :=
  {σ : L ≃ₐ[K] L | ∃ (𝔔 : Ideal (RingOfIntegers L)),
    𝔔.IsPrime ∧ 𝔔.LiesOver 𝔭.asIdeal ∧
    IsArithFrobAt (RingOfIntegers K) σ 𝔔}

def primesWithFrobInSet (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (C : Set (L ≃ₐ[K] L)) : Set (Prime' K) :=
  {𝔭 : Prime' K | GlobalCFT.IsUnramifiedIn K L 𝔭 ∧ FrobeniusConjClass K L 𝔭 ⊆ C}

noncomputable def liftToGalLE {K L : Type*} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) :
    L ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers σ)] L :=
  IntermediateField.fixingSubgroupEquiv
    (IntermediateField.fixedField (Subgroup.zpowers σ))
    ⟨σ, by rw [IntermediateField.fixingSubgroup_fixedField]; exact Subgroup.mem_zpowers σ⟩

end
