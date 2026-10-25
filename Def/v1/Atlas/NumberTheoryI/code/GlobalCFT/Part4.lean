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
import Theorem.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part3


noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

section ArtinSymbol

universe v

variable (K : Type v) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

noncomputable def proposition_22_4_iso_aux (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (hCong₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
    (hCong₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
    (𝔫 : Modulus K) (h𝔪₁ : Modulus.dvd 𝔪₁ 𝔫) (h𝔪₂ : Modulus.dvd 𝔪₂ 𝔫)
    (heq : Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 h𝔪₁) 𝒞₁ =
           Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 h𝔪₂) 𝒞₂) :
    FracIdealsCoprime K 𝔪₁ ⧸ 𝒞₁ ≃* FracIdealsCoprime K 𝔪₂ ⧸ 𝒞₂ := by

  let ι₁ := FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 h𝔪₁
  let ι₂ := FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 h𝔪₂

  haveI normal₁ : (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁)).Normal :=
    Subgroup.normal_of_comm 𝒞₁
  haveI normal₂ : (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂)).Normal :=
    Subgroup.normal_of_comm 𝒞₂

  let f₁ := (QuotientGroup.mk' 𝒞₁).comp ι₁
  let f₂ := (QuotientGroup.mk' 𝒞₂).comp ι₂

  have surj₁ : Function.Surjective f₁ :=
    FracIdealsCoprime.inclusion_mk_surjective K 𝔪₁ 𝔫 h𝔪₁ 𝒞₁ hCong₁
  have surj₂ : Function.Surjective f₂ :=
    FracIdealsCoprime.inclusion_mk_surjective K 𝔪₂ 𝔫 h𝔪₂ 𝒞₂ hCong₂


  have ker_eq₁ : f₁.ker = Subgroup.comap ι₁ 𝒞₁ := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, f₁, MonoidHom.comp_apply]
    exact QuotientGroup.eq_one_iff (ι₁ x)
  have ker_eq₂ : f₂.ker = Subgroup.comap ι₂ 𝒞₂ := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, f₂, MonoidHom.comp_apply]
    exact QuotientGroup.eq_one_iff (ι₂ x)

  have heq_ker : f₁.ker = f₂.ker := by rw [ker_eq₁, ker_eq₂, heq]

  exact (QuotientGroup.quotientKerEquivOfSurjective f₁ surj₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq heq_ker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f₂ surj₂))

noncomputable def proposition_22_4_iso (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (hCong₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
    (hCong₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
    (h : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) :
    FracIdealsCoprime K 𝔪₁ ⧸ 𝒞₁ ≃* FracIdealsCoprime K 𝔪₂ ⧸ 𝒞₂ := by
  choose 𝔫 h𝔪₁ h𝔪₂ heq using h
  exact proposition_22_4_iso_aux K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ hCong₁ hCong₂ 𝔫 h𝔪₁ h𝔪₂ heq

end ArtinSymbol
end
