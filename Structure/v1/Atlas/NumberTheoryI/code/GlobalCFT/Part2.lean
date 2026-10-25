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
import Def.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part10


noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

section ArtinSymbol

universe v

variable (K : Type v) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

structure IsHilbertClassField (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsAbelianExtension K L] : Prop where
  finiteDimensional : FiniteDimensional K L
  everywhere_unramified : ∀ 𝔭 : Prime' K, IsUnramifiedIn K L 𝔭
  maximal :
    ∀ (M : Type u) [Field M] [NumberField M] [Algebra K M] [IsAbelianExtension K M]
      [FiniteDimensional K M],
      (∀ 𝔭 : Prime' K, IsUnramifiedIn K M 𝔭) → Nonempty (M →ₐ[K] L)

end GlobalCFT

open Ideles

structure GlobalArtinMap (K : Type*) [Field K] [NumberField K] where
  I : Type*
  [instPreorder : Preorder I]
  GalLK : I → Type*
  [instFintype : ∀ i, Fintype (GalLK i)]
  [instCommGroup : ∀ i, CommGroup (GalLK i)]
  restrictMap : ∀ {i j : I}, i ≤ j → GalLK j →* GalLK i
  artinMap : ∀ i, IdeleGroup K →* GalLK i
  artinMap_compat : ∀ {i j : I} (h : i ≤ j) (a : IdeleGroup K),
    restrictMap h (artinMap j a) = artinMap i a
  GalAb : Type*
  [galAb_group : CommGroup GalAb]
  [galAb_topologicalSpace : TopologicalSpace GalAb]
  [galAb_topologicalGroup : IsTopologicalGroup GalAb]
  [galAb_compactSpace : CompactSpace GalAb]
  artinHom : IdeleGroup K →* GalAb
  artinHom_continuous : Continuous artinHom
  proj : ∀ i, GalAb →* GalLK i
  artinMap_eq_proj : ∀ i (a : IdeleGroup K), artinMap i a = proj i (artinHom a)
  artinMap_surjective : ∀ i, Function.Surjective (artinMap i)
  proj_jointly_injective : ∀ g : GalAb, (∀ i, proj i g = 1) → g = 1
  proj_compat : ∀ {i j : I} (h : i ≤ j) (g : GalAb),
    restrictMap h (proj j g) = proj i g
  principalInKer : principalIdeles K ≤ MonoidHom.ker artinHom
  normSubgroup : ∀ i, Subgroup (IdeleClassGroup K)
  normSubgroup_normal : ∀ i, (normSubgroup i).Normal
  artinMapCK_surjective : ∀ i, Function.Surjective
    ((proj i).comp (QuotientGroup.lift (principalIdeles K) artinHom principalInKer))
  ker_eq_normSubgroup : ∀ i, MonoidHom.ker
    ((proj i).comp (QuotientGroup.lift (principalIdeles K) artinHom principalInKer)) =
    normSubgroup i

end
