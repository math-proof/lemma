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
import Def.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part3


noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

section ArtinSymbol

universe v

variable (K : Type v) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

theorem congruenceSubgroupEquiv_refl (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) :
    CongruenceSubgroupEquiv K 𝔪 𝔪 𝒞 𝒞 := by
  refine ⟨𝔪, fun v => le_refl _, fun v => le_refl _, rfl⟩

theorem congruenceSubgroupEquiv_symm (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (h : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) :
    CongruenceSubgroupEquiv K 𝔪₂ 𝔪₁ 𝒞₂ 𝒞₁ := by
  obtain ⟨𝔫, h₁, h₂, heq⟩ := h
  exact ⟨𝔫, h₂, h₁, heq.symm⟩

theorem FracIdealsCoprime.inclusion_comp (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 𝔭 : Modulus K) (h₁ : Modulus.dvd 𝔪 𝔫) (h₂ : Modulus.dvd 𝔫 𝔭)
    (h₃ : Modulus.dvd 𝔪 𝔭) :
    ∀ x : FracIdealsCoprime K 𝔭,
      (FracIdealsCoprime.inclusion K 𝔪 𝔫 h₁)
        ((FracIdealsCoprime.inclusion K 𝔫 𝔭 h₂) x) =
      (FracIdealsCoprime.inclusion K 𝔪 𝔭 h₃) x := by
  intro x
  simp only [FracIdealsCoprime.inclusion, Subgroup.inclusion]
  rfl


theorem FracIdealsCoprime.exists_ray_mul_coprime (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (x : FracIdealsCoprime K 𝔪) :
    ∃ (r : FracIdealsCoprime K 𝔪),
      r ∈ RayGroup K 𝔪 ∧
      (x * r⁻¹).val ∈ FracIdealsCoprime_subgroup K 𝔫 := by

  have hgcd : 𝔪.gcd 𝔫 = 𝔪 := by
    have hfun : (𝔪.gcd 𝔫).toFun = 𝔪.toFun := by
      funext v; exact Nat.min_eq_left (h v)
    rcases 𝔪 with ⟨f, hf1, hf2, hf3⟩
    rcases 𝔫 with ⟨g, hg1, hg2, hg3⟩
    simp only [Modulus.gcd, Modulus.mk.injEq] at hfun ⊢
    exact hfun

  have hcrt := theorem_8_5_coprime_CRT_core K 𝔪 𝔫
  rw [hgcd] at hcrt


  have hx_mem : x.val ∈ FracIdealsCoprime_subgroup K 𝔪 := x.prop
  have hx_sup := hcrt hx_mem
  rw [Subgroup.mem_sup] at hx_sup
  obtain ⟨y, hy, z, hz, hxyz⟩ := hx_sup
  have hz_ray : z ∈ RayGroup.toAmbientSubgroup K 𝔪 := (Subgroup.mem_inf.mp hz).2
  have hz_cop : z ∈ FracIdealsCoprime_subgroup K 𝔪 := (Subgroup.mem_inf.mp hz).1

  rw [RayGroup.toAmbientSubgroup] at hz_ray
  obtain ⟨r₀, hr₀_ray, hr₀_eq⟩ := Subgroup.mem_map.mp hz_ray


  let r : FracIdealsCoprime K 𝔪 := r₀
  refine ⟨r, hr₀_ray, ?_⟩


  suffices h : (x * r⁻¹).val = y by rw [h]; exact hy
  change x.val * r.val⁻¹ = y
  have : r.val = z := hr₀_eq
  rw [this]

  rw [← hxyz, mul_inv_cancel_right]

theorem FracIdealsCoprime.approx_theorem (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (x : FracIdealsCoprime K 𝔪) :
    ∃ (y : FracIdealsCoprime K 𝔫) (r : FracIdealsCoprime K 𝔪),
      r ∈ RayGroup K 𝔪 ∧
      x = (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) y * r := by

  obtain ⟨r, hr_ray, hr_coprime⟩ := FracIdealsCoprime.exists_ray_mul_coprime K 𝔪 𝔫 h x

  refine ⟨⟨(x * r⁻¹).val, hr_coprime⟩, r, hr_ray, ?_⟩


  have incl_eq : (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) ⟨(x * r⁻¹).val, hr_coprime⟩ = x * r⁻¹ := by
    apply Subtype.ext
    simp only [FracIdealsCoprime.inclusion]
    rfl
  rw [incl_eq]
  group

theorem FracIdealsCoprime.inclusion_mk_surjective (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    [𝒞.Normal]
    (hCong : IsCongruenceSubgroup K 𝔪 𝒞) :
    Function.Surjective ((QuotientGroup.mk' 𝒞).comp (FracIdealsCoprime.inclusion K 𝔪 𝔫 h)) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective 𝒞 q

  obtain ⟨y, r, hr_ray, hx_eq⟩ := FracIdealsCoprime.approx_theorem K 𝔪 𝔫 h x
  refine ⟨y, ?_⟩
  simp only [MonoidHom.comp_apply]


  rw [hx_eq, map_mul]
  have hr_mem : r ∈ 𝒞 := hCong.contains_ray hr_ray
  have : (QuotientGroup.mk' 𝒞) r = 1 :=
    (QuotientGroup.eq_one_iff r).mpr hr_mem
  rw [this, mul_one]

theorem congruenceSubgroupEquiv_trans (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ 𝔪₃ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (𝒞₃ : Subgroup (FracIdealsCoprime K 𝔪₃))
    (h₁₂ : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂)
    (h₂₃ : CongruenceSubgroupEquiv K 𝔪₂ 𝔪₃ 𝒞₂ 𝒞₃) :
    CongruenceSubgroupEquiv K 𝔪₁ 𝔪₃ 𝒞₁ 𝒞₃ := by
  obtain ⟨𝔫₁₂, h₁_12, h₂_12, heq₁₂⟩ := h₁₂
  obtain ⟨𝔫₂₃, h₂_23, h₃_23, heq₂₃⟩ := h₂₃

  let 𝔫 := Modulus.lcm 𝔫₁₂ 𝔫₂₃
  have hd₁₂_n : Modulus.dvd 𝔫₁₂ 𝔫 := fun v => le_max_left _ _
  have hd₂₃_n : Modulus.dvd 𝔫₂₃ 𝔫 := fun v => le_max_right _ _
  have hd₁_n : Modulus.dvd 𝔪₁ 𝔫 := fun v => le_trans (h₁_12 v) (hd₁₂_n v)
  have hd₂_n₁ : Modulus.dvd 𝔪₂ 𝔫 := fun v => le_trans (h₂_12 v) (hd₁₂_n v)
  have hd₂_n₂ : Modulus.dvd 𝔪₂ 𝔫 := fun v => le_trans (h₂_23 v) (hd₂₃_n v)
  have hd₃_n : Modulus.dvd 𝔪₃ 𝔫 := fun v => le_trans (h₃_23 v) (hd₂₃_n v)
  refine ⟨𝔫, hd₁_n, hd₃_n, ?_⟩


  ext x
  simp only [Subgroup.mem_comap]
  constructor
  · intro hx₁


    have step1 : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₁₂ h₂_12)
        ((FracIdealsCoprime.inclusion K 𝔫₁₂ 𝔫 hd₁₂_n) x) ∈ 𝒞₂ := by
      rw [← Subgroup.mem_comap, ← heq₁₂, Subgroup.mem_comap]
      rw [FracIdealsCoprime.inclusion_comp K 𝔪₁ 𝔫₁₂ 𝔫 h₁_12 hd₁₂_n hd₁_n]
      exact hx₁


    have step1' : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 hd₂_n₁) x ∈ 𝒞₂ := by
      rw [← FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔫₁₂ 𝔫 h₂_12 hd₁₂_n hd₂_n₁]
      exact step1

    have step2 : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₂₃ h₂_23)
        ((FracIdealsCoprime.inclusion K 𝔫₂₃ 𝔫 hd₂₃_n) x) ∈ 𝒞₂ := by
      rw [FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔫₂₃ 𝔫 h₂_23 hd₂₃_n hd₂_n₂]
      exact step1'

    have step3 : (FracIdealsCoprime.inclusion K 𝔪₃ 𝔫₂₃ h₃_23)
        ((FracIdealsCoprime.inclusion K 𝔫₂₃ 𝔫 hd₂₃_n) x) ∈ 𝒞₃ := by
      have : (FracIdealsCoprime.inclusion K 𝔫₂₃ 𝔫 hd₂₃_n) x ∈
          Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₂₃ h₂_23) 𝒞₂ := by
        rw [Subgroup.mem_comap]; exact step2
      rw [heq₂₃] at this
      exact this

    rw [← FracIdealsCoprime.inclusion_comp K 𝔪₃ 𝔫₂₃ 𝔫 h₃_23 hd₂₃_n hd₃_n]
    exact step3

  · intro hx₃

    have step1 : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₂₃ h₂_23)
        ((FracIdealsCoprime.inclusion K 𝔫₂₃ 𝔫 hd₂₃_n) x) ∈ 𝒞₂ := by
      rw [← Subgroup.mem_comap, heq₂₃, Subgroup.mem_comap]
      rw [FracIdealsCoprime.inclusion_comp K 𝔪₃ 𝔫₂₃ 𝔫 h₃_23 hd₂₃_n hd₃_n]
      exact hx₃
    have step1' : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 hd₂_n₂) x ∈ 𝒞₂ := by
      rw [← FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔫₂₃ 𝔫 h₂_23 hd₂₃_n hd₂_n₂]
      exact step1
    have step2 : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₁₂ h₂_12)
        ((FracIdealsCoprime.inclusion K 𝔫₁₂ 𝔫 hd₁₂_n) x) ∈ 𝒞₂ := by
      rw [FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔫₁₂ 𝔫 h₂_12 hd₁₂_n hd₂_n₁]
      exact step1'
    have step3 : (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫₁₂ h₁_12)
        ((FracIdealsCoprime.inclusion K 𝔫₁₂ 𝔫 hd₁₂_n) x) ∈ 𝒞₁ := by
      have : (FracIdealsCoprime.inclusion K 𝔫₁₂ 𝔫 hd₁₂_n) x ∈
          Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₁₂ h₂_12) 𝒞₂ := by
        rw [Subgroup.mem_comap]; exact step2
      rw [← heq₁₂] at this
      exact this

    rw [← FracIdealsCoprime.inclusion_comp K 𝔪₁ 𝔫₁₂ 𝔫 h₁_12 hd₁₂_n hd₁_n]
    exact step3

end ArtinSymbol
end
