/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.NumberTheoryI.code.RayClassFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ideles
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdeleNorm
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor227
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ch22NormGroup
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Prop2219
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Ideles
import sympy.atlas.v1.Atlas.NumberTheoryI.code.IdeleNorm
import sympy.atlas.v1.Atlas.NumberTheoryI.code.KroneckerWeber
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Cor227
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Chapter3.FiniteApproximation
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Ch22NormGroup
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Prop2219
noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

section ArtinSymbol

universe v

variable (K : Type v) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

def ArtinSymbol
    (𝔔 : Ideal (RingOfIntegers L))
    [𝔔.IsPrime] [Finite (RingOfIntegers L ⧸ 𝔔)] :
    (L ≃ₐ[K] L) :=
  arithFrobAt (RingOfIntegers K) (L ≃ₐ[K] L) 𝔔

structure IsCongruenceSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) : Prop where
  contains_ray : RayGroup K 𝔪 ≤ 𝒞


lemma FracIdealsCoprime_subgroup_le (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫) :
    FracIdealsCoprime_subgroup K 𝔫 ≤ FracIdealsCoprime_subgroup K 𝔪 := by
  intro I hI v hv
  apply hI v
  intro h0
  exact absurd (Nat.le_zero.mp (h0 ▸ h (Place.finite v))) hv

noncomputable def FracIdealsCoprime.inclusion (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫) :
    FracIdealsCoprime K 𝔫 →* FracIdealsCoprime K 𝔪 :=
  Subgroup.inclusion (FracIdealsCoprime_subgroup_le K 𝔪 𝔫 h)

lemma IsRayGenerator_inclusion (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (I : FracIdealsCoprime K 𝔫) (hI : IsRayGenerator 𝔫 I) :
    IsRayGenerator 𝔪 (Subgroup.inclusion (FracIdealsCoprime_subgroup_le K 𝔪 𝔫 h) I) := by
  obtain ⟨α, hprinc, hcong, hsign⟩ := hI
  refine ⟨α, ?_, ?_, ?_⟩
  ·
    simp only [Subgroup.coe_inclusion]
    exact hprinc
  ·
    intro v hv
    have hv_n : 𝔫 (Place.finite v) ≠ 0 := by
      intro h0; exact hv (Nat.eq_zero_of_le_zero (h0 ▸ h (Place.finite v)))
    have hle : (𝔪 (Place.finite v) : ℤ) ≤ (𝔫 (Place.finite v) : ℤ) :=
      Int.ofNat_le.mpr (h (Place.finite v))
    calc v.valuation K ((α : K) - 1)
        ≤ ↑(Multiplicative.ofAdd (-(𝔫 (Place.finite v) : ℤ))) := hcong v hv_n
      _ ≤ ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ))) := by
          simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le]
          linarith
  ·
    intro w hw
    exact hsign w (fun h0 => hw (Nat.eq_zero_of_le_zero (h0 ▸ h (Place.infinite w))))

theorem RayGroup.inclusion_le (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫) :
    ∀ x : FracIdealsCoprime K 𝔫,
      x ∈ RayGroup K 𝔫 → (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) x ∈ RayGroup K 𝔪 := by

  intro x hx
  let f := FracIdealsCoprime.inclusion K 𝔪 𝔫 h

  have hmem : f x ∈ Subgroup.map f (RayGroup K 𝔫) := ⟨x, hx, rfl⟩

  rw [show RayGroup K 𝔫 = Subgroup.closure {I | IsRayGenerator 𝔫 I} from rfl,
      MonoidHom.map_closure] at hmem

  have himg_sub : f '' {I | IsRayGenerator 𝔫 I} ⊆ {I | IsRayGenerator 𝔪 I} := by
    rintro _ ⟨I, hI, rfl⟩
    exact IsRayGenerator_inclusion K 𝔪 𝔫 h I hI
  exact Subgroup.closure_mono himg_sub hmem

def CongruenceSubgroupEquiv (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂)) : Prop :=
  ∃ (𝔫 : Modulus K) (h₁ : Modulus.dvd 𝔪₁ 𝔫) (h₂ : Modulus.dvd 𝔪₂ 𝔫),
    Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 h₁) 𝒞₁ =
    Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 h₂) 𝒞₂

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

lemma FracIdealsCoprime.subtype_inclusion (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (x : FracIdealsCoprime K 𝔫) :
    (FracIdealsCoprime_subgroup K 𝔪).subtype
      (FracIdealsCoprime.inclusion K 𝔪 𝔫 h x) =
    (FracIdealsCoprime_subgroup K 𝔫).subtype x := by
  simp only [FracIdealsCoprime.inclusion, Subgroup.inclusion]
  rfl

lemma mem_comap_inclusion_iff_mem_toAmbientSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (x : FracIdealsCoprime K 𝔫) :
    x ∈ Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) 𝒞 ↔
    (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
      𝒞.map (FracIdealsCoprime_subgroup K 𝔪).subtype := by
  rw [Subgroup.mem_comap]
  constructor
  · intro hx
    exact ⟨FracIdealsCoprime.inclusion K 𝔪 𝔫 h x, hx,
      FracIdealsCoprime.subtype_inclusion K 𝔪 𝔫 h x⟩
  · rintro ⟨y, hy, heq⟩
    have hval : FracIdealsCoprime.inclusion K 𝔪 𝔫 h x = y := by
      apply Subtype.ext
      have h1 := FracIdealsCoprime.subtype_inclusion K 𝔪 𝔫 h x
      simp only [Subgroup.coe_subtype] at h1 heq
      exact h1.trans heq.symm
    rw [hval]
    exact hy

theorem isEquiv_to_congruenceSubgroupEquiv (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (h₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
    (h₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
    (h_isEquiv : (⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩ : CongruenceSubgroupPair K).IsEquiv
                  ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩) :
    CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ := by
  set p₁ : CongruenceSubgroupPair K := ⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩
  set p₂ : CongruenceSubgroupPair K := ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩
  set 𝔫 := Modulus.lcm 𝔪₁ 𝔪₂
  have hdvd₁ : Modulus.dvd 𝔪₁ 𝔫 := RayClassField.Modulus.dvd_lcm_left 𝔪₁ 𝔪₂
  have hdvd₂ : Modulus.dvd 𝔪₂ 𝔫 := RayClassField.Modulus.dvd_lcm_right 𝔪₁ 𝔪₂
  refine ⟨𝔫, hdvd₁, hdvd₂, ?_⟩
  ext x
  rw [mem_comap_inclusion_iff_mem_toAmbientSubgroup K 𝔪₁ 𝔫 hdvd₁ 𝒞₁ x]
  rw [mem_comap_inclusion_iff_mem_toAmbientSubgroup K 𝔪₂ 𝔫 hdvd₂ 𝒞₂ x]
  have hx_in_I₁ : (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
      FracIdealsCoprime_subgroup K 𝔪₁ :=
    FracIdealsCoprime_subgroup_le K 𝔪₁ 𝔫 hdvd₁ x.2
  have hx_in_I₂ : (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
      FracIdealsCoprime_subgroup K 𝔪₂ :=
    FracIdealsCoprime_subgroup_le K 𝔪₂ 𝔫 hdvd₂ x.2
  constructor
  · intro hx_amb₁
    have : (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
        FracIdealsCoprime_subgroup K 𝔪₂ ⊓ p₁.toAmbientSubgroup :=
      ⟨hx_in_I₂, hx_amb₁⟩
    rw [← h_isEquiv] at this
    exact this.2
  · intro hx_amb₂
    have : (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
        FracIdealsCoprime_subgroup K 𝔪₁ ⊓ p₂.toAmbientSubgroup :=
      ⟨hx_in_I₁, hx_amb₂⟩
    rw [h_isEquiv] at this
    exact this.2

theorem isEquiv_of_dvd_comap (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (hdvd : Modulus.dvd 𝔪 𝔫)
    (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (𝒞_𝔫 : Subgroup (FracIdealsCoprime K 𝔫))
    (h_cong_𝔫 : IsCongruenceSubgroup K 𝔫 𝒞_𝔫)
    (h_eq : 𝒞_𝔫 = Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd) 𝒞) :
    (⟨𝔪, 𝒞, h_cong.contains_ray⟩ : CongruenceSubgroupPair K).IsEquiv
      ⟨𝔫, 𝒞_𝔫, h_cong_𝔫.contains_ray⟩ := by


  show FracIdealsCoprime_subgroup K 𝔪 ⊓
      (𝒞_𝔫.map (FracIdealsCoprime_subgroup K 𝔫).subtype) =
    FracIdealsCoprime_subgroup K 𝔫 ⊓
      (𝒞.map (FracIdealsCoprime_subgroup K 𝔪).subtype)
  ext a
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  ·
    rintro ⟨ha_cop_m, z, hz_in, hz_eq⟩
    constructor
    · rw [← hz_eq]; exact z.2
    ·
      have hz_comap : FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd z ∈ 𝒞 := by
        have : z ∈ Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd) 𝒞 :=
          h_eq ▸ hz_in
        exact Subgroup.mem_comap.mp this
      exact ⟨FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd z, hz_comap, by
        have := FracIdealsCoprime.subtype_inclusion K 𝔪 𝔫 hdvd z
        simp only [Subgroup.coe_subtype] at this hz_eq ⊢
        exact this.symm.trans hz_eq⟩
  ·
    rintro ⟨ha_cop_n, c, hc_in, hc_eq⟩
    refine ⟨?_, ?_⟩
    ·
      rw [← hc_eq]; exact c.2
    ·
      refine ⟨⟨a, ha_cop_n⟩, ?_, rfl⟩

      rw [h_eq]

      have hval : FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd ⟨a, ha_cop_n⟩ = c := by
        apply Subtype.ext
        have h1 := FracIdealsCoprime.subtype_inclusion K 𝔪 𝔫 hdvd (⟨a, ha_cop_n⟩ : FracIdealsCoprime K 𝔫)
        simp only [Subgroup.coe_subtype] at h1 hc_eq
        exact h1.trans hc_eq.symm
      exact Subgroup.mem_comap.mpr (hval ▸ hc_in)

theorem congruenceSubgroupEquiv_to_isEquiv (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (h₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
    (h₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
    (h_equiv : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) :
    (⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩ : CongruenceSubgroupPair K).IsEquiv
      ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩ := by
  obtain ⟨𝔫, hdvd₁, hdvd₂, h_comap_eq⟩ := h_equiv
  set p₁ : CongruenceSubgroupPair K := ⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩
  set p₂ : CongruenceSubgroupPair K := ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩

  set 𝒞_𝔫 := Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 hdvd₁) 𝒞₁

  have h_cong_𝔫 : IsCongruenceSubgroup K 𝔫 𝒞_𝔫 := by
    constructor
    intro z hz
    rw [Subgroup.mem_comap]
    exact h₁.contains_ray (RayGroup.inclusion_le K 𝔪₁ 𝔫 hdvd₁ z hz)
  set p_𝔫 : CongruenceSubgroupPair K := ⟨𝔫, 𝒞_𝔫, h_cong_𝔫.contains_ray⟩

  have h_equiv₁ : p₁.IsEquiv p_𝔫 :=
    isEquiv_of_dvd_comap K 𝔪₁ 𝔫 hdvd₁ 𝒞₁ h₁ 𝒞_𝔫 h_cong_𝔫 rfl

  have h_eq₂ : 𝒞_𝔫 = Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 hdvd₂) 𝒞₂ :=
    h_comap_eq

  have h_equiv₂ : p₂.IsEquiv p_𝔫 :=
    isEquiv_of_dvd_comap K 𝔪₂ 𝔫 hdvd₂ 𝒞₂ h₂ 𝒞_𝔫 h_cong_𝔫 h_eq₂


  exact h_equiv₁.trans' h_equiv₂.symm'

theorem proposition_22_6 (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (h₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
    (h₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
    (h_equiv : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) :
    ∃ 𝒞 : Subgroup (FracIdealsCoprime K (Modulus.gcd 𝔪₁ 𝔪₂)),
      IsCongruenceSubgroup K (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞 ∧
      CongruenceSubgroupEquiv K 𝔪₁ (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞₁ 𝒞 ∧
      CongruenceSubgroupEquiv K 𝔪₂ (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞₂ 𝒞 := by

  set p₁ : CongruenceSubgroupPair K := ⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩
  set p₂ : CongruenceSubgroupPair K := ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩
  have h_isEquiv : p₁.IsEquiv p₂ :=
    congruenceSubgroupEquiv_to_isEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ h₁ h₂ h_equiv

  obtain ⟨⟨p_mod, p_sub, p_ray⟩, hp_mod, hp_equiv₁, hp_equiv₂⟩ :=
    RayClassField.proposition_22_6 p₁ p₂ h_isEquiv

  simp only [CongruenceSubgroupPair.modulus] at hp_mod
  subst hp_mod

  have h_cong : IsCongruenceSubgroup K (Modulus.gcd 𝔪₁ 𝔪₂) p_sub := by
    constructor; exact p_ray
  refine ⟨p_sub, h_cong, ?_, ?_⟩
  · exact isEquiv_to_congruenceSubgroupEquiv K 𝔪₁ (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞₁ p_sub h₁ h_cong
      hp_equiv₁
  · exact isEquiv_to_congruenceSubgroupEquiv K 𝔪₂ (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞₂ p_sub h₂ h_cong
      hp_equiv₂

theorem equiv_moduli_closed_under_gcd (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (𝔪₁ 𝔪₂ : Modulus K)
    (h₁ : ∃ 𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁),
      IsCongruenceSubgroup K 𝔪₁ 𝒞₁ ∧ CongruenceSubgroupEquiv K 𝔪 𝔪₁ 𝒞 𝒞₁)
    (h₂ : ∃ 𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂),
      IsCongruenceSubgroup K 𝔪₂ 𝒞₂ ∧ CongruenceSubgroupEquiv K 𝔪 𝔪₂ 𝒞 𝒞₂) :
    ∃ 𝒞g : Subgroup (FracIdealsCoprime K (Modulus.gcd 𝔪₁ 𝔪₂)),
      IsCongruenceSubgroup K (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞g ∧
      CongruenceSubgroupEquiv K 𝔪 (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞 𝒞g := by
  obtain ⟨𝒞₁, hc₁, he₁⟩ := h₁
  obtain ⟨𝒞₂, hc₂, he₂⟩ := h₂

  have h_equiv₁₂ : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ :=
    congruenceSubgroupEquiv_trans K 𝔪₁ 𝔪 𝔪₂ 𝒞₁ 𝒞 𝒞₂
      (congruenceSubgroupEquiv_symm K 𝔪 𝔪₁ 𝒞 𝒞₁ he₁) he₂
  obtain ⟨𝒞g, hcg, heg₁, heg₂⟩ := proposition_22_6 K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ hc₁ hc₂ h_equiv₁₂
  exact ⟨𝒞g, hcg, congruenceSubgroupEquiv_trans K 𝔪 𝔪₁ (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞 𝒞₁ 𝒞g he₁ heg₁⟩

lemma gcd_weight_lt_of_not_dvd {K : Type u} [Field K] [NumberField K]
    {𝔪₁ 𝔪₂ : Modulus K} (h : ¬ 𝔪₁.dvd 𝔪₂) :
    (𝔪₁.gcd 𝔪₂).weight < 𝔪₁.weight := by
  simp only [Modulus.dvd, not_forall, not_le] at h
  obtain ⟨v₀, hv₀⟩ := h
  have hgcd_v₀ : (𝔪₁.gcd 𝔪₂).toFun v₀ < 𝔪₁.toFun v₀ := by
    simp only [Modulus.gcd]
    exact lt_of_le_of_lt (min_le_right _ _) hv₀
  have hgcd_le : ∀ v, (𝔪₁.gcd 𝔪₂).toFun v ≤ 𝔪₁.toFun v := fun v => by
    simp only [Modulus.gcd]; exact min_le_left _ _
  have hv₀_supp : v₀ ∈ 𝔪₁.finite_support.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    omega
  have hsub : (𝔪₁.gcd 𝔪₂).finite_support.toFinset ⊆ 𝔪₁.finite_support.toFinset := by
    intro v hv
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv ⊢
    intro heq
    exact hv (by simp only [Modulus.gcd]; omega)
  unfold Modulus.weight
  calc (𝔪₁.gcd 𝔪₂).finite_support.toFinset.sum (𝔪₁.gcd 𝔪₂).toFun
      ≤ 𝔪₁.finite_support.toFinset.sum (𝔪₁.gcd 𝔪₂).toFun := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ < 𝔪₁.finite_support.toFinset.sum 𝔪₁.toFun := by
        exact Finset.sum_lt_sum (fun v _ => hgcd_le v) ⟨v₀, hv₀_supp, hgcd_v₀⟩

theorem exists_minimal_equiv_modulus (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
    ∃ (𝔠 : Modulus K),
      (∃ 𝒞₀ : Subgroup (FracIdealsCoprime K 𝔠),
        IsCongruenceSubgroup K 𝔠 𝒞₀ ∧ CongruenceSubgroupEquiv K 𝔪 𝔠 𝒞 𝒞₀) ∧
      ∀ (𝔫 : Modulus K),
        (∃ 𝒟 : Subgroup (FracIdealsCoprime K 𝔫),
          IsCongruenceSubgroup K 𝔫 𝒟 ∧ CongruenceSubgroupEquiv K 𝔪 𝔫 𝒞 𝒟) →
        Modulus.dvd 𝔠 𝔫 := by


  suffices h : ∀ (n : ℕ) (𝔪' : Modulus K) (𝒞' : Subgroup (FracIdealsCoprime K 𝔪')),
      IsCongruenceSubgroup K 𝔪' 𝒞' →
      CongruenceSubgroupEquiv K 𝔪 𝔪' 𝒞 𝒞' →
      𝔪'.weight = n →
      ∃ (𝔠 : Modulus K),
        (∃ 𝒞₀ : Subgroup (FracIdealsCoprime K 𝔠),
          IsCongruenceSubgroup K 𝔠 𝒞₀ ∧ CongruenceSubgroupEquiv K 𝔪 𝔠 𝒞 𝒞₀) ∧
        ∀ (𝔫 : Modulus K),
          (∃ 𝒟 : Subgroup (FracIdealsCoprime K 𝔫),
            IsCongruenceSubgroup K 𝔫 𝒟 ∧ CongruenceSubgroupEquiv K 𝔪 𝔫 𝒞 𝒟) →
          Modulus.dvd 𝔠 𝔫 from
    h 𝔪.weight 𝔪 𝒞 h_cong (congruenceSubgroupEquiv_refl K 𝔪 𝒞) rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro 𝔪' 𝒞' h_cong' h_equiv' h_wt

  by_cases hmin : ∀ (𝔫 : Modulus K),
      (∃ 𝒟 : Subgroup (FracIdealsCoprime K 𝔫),
        IsCongruenceSubgroup K 𝔫 𝒟 ∧ CongruenceSubgroupEquiv K 𝔪 𝔫 𝒞 𝒟) →
      Modulus.dvd 𝔪' 𝔫
  ·
    exact ⟨𝔪', ⟨⟨𝒞', h_cong', h_equiv'⟩, hmin⟩⟩
  ·
    push Not at hmin

    obtain ⟨𝔫, ⟨𝒟, h_congD, h_equivD⟩, hndvd⟩ := hmin

    obtain ⟨𝒞g, h_congG, h_equivG⟩ :=
      equiv_moduli_closed_under_gcd K 𝔪 𝒞 𝔪' 𝔫
        ⟨𝒞', h_cong', h_equiv'⟩ ⟨𝒟, h_congD, h_equivD⟩

    have h_wt_lt : (Modulus.gcd 𝔪' 𝔫).weight < n := by
      rw [← h_wt]
      exact gcd_weight_lt_of_not_dvd hndvd

    exact ih (Modulus.gcd 𝔪' 𝔫).weight h_wt_lt
      (Modulus.gcd 𝔪' 𝔫) 𝒞g h_congG h_equivG rfl

theorem corollary_22_7 (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
    ∃! (𝔠 : Modulus K),
      (∃ 𝒞₀ : Subgroup (FracIdealsCoprime K 𝔠),
        IsCongruenceSubgroup K 𝔠 𝒞₀ ∧ CongruenceSubgroupEquiv K 𝔪 𝔠 𝒞 𝒞₀) ∧
      ∀ (𝔫 : Modulus K),
        (∃ 𝒟 : Subgroup (FracIdealsCoprime K 𝔫),
          IsCongruenceSubgroup K 𝔫 𝒟 ∧ CongruenceSubgroupEquiv K 𝔪 𝔫 𝒞 𝒟) →
        Modulus.dvd 𝔠 𝔫 := by

  obtain ⟨𝔠, ⟨h_exist, h_dvd⟩⟩ := exists_minimal_equiv_modulus K 𝔪 𝒞 h_cong
  refine ⟨𝔠, ⟨h_exist, h_dvd⟩, ?_⟩

  intro 𝔠' ⟨h_exist', h_dvd'⟩

  have h1 : Modulus.dvd 𝔠 𝔠' := h_dvd 𝔠' h_exist'
  have h2 : Modulus.dvd 𝔠' 𝔠 := h_dvd' 𝔠 h_exist
  have htf : 𝔠'.toFun = 𝔠.toFun := funext (fun v => le_antisymm (h2 v) (h1 v))
  rcases 𝔠 with ⟨f₁, hs₁, hi₁, hc₁⟩
  rcases 𝔠' with ⟨f₂, hs₂, hi₂, hc₂⟩
  congr 1

noncomputable def conductorOfCongruenceSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) : Modulus K :=
  (corollary_22_7 K 𝔪 𝒞 h_cong).choose

def IsPrimitive (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) : Prop :=
  conductorOfCongruenceSubgroup K 𝔪 𝒞 h_cong = 𝔪

abbrev RayClassCharacter (K : Type u) [Field K] [NumberField K] (𝔪 : Modulus K) : Type u :=
  RayClassGroup K 𝔪 →* ℂˣ

def RayClassGroup.mapOfDvd {K : Type u} [Field K] [NumberField K]
    {𝔪₁ 𝔪₂ : Modulus K} (h : Modulus.dvd 𝔪₁ 𝔪₂) :
    RayClassGroup K 𝔪₂ →* RayClassGroup K 𝔪₁ :=
  QuotientGroup.map (RayGroup K 𝔪₂) (RayGroup K 𝔪₁)
    (FracIdealsCoprime.inclusion K 𝔪₁ 𝔪₂ h)
    (fun x hx => RayGroup.inclusion_le K 𝔪₁ 𝔪₂ h x hx)

def IsInducedBy (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K) (h : Modulus.dvd 𝔪₁ 𝔪₂)
    (χ₁ : RayClassCharacter K 𝔪₁) (χ₂ : RayClassCharacter K 𝔪₂) : Prop :=
  χ₂ = χ₁.comp (RayClassGroup.mapOfDvd h)

def kernelCongruenceSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) : Subgroup (FracIdealsCoprime K 𝔪) :=
  Subgroup.comap (QuotientGroup.mk' (RayGroup K 𝔪)) (MonoidHom.ker χ)

theorem kernelCongruenceSubgroup_isCong (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) :
    IsCongruenceSubgroup K 𝔪 (kernelCongruenceSubgroup K 𝔪 χ) := by
  refine ⟨fun x hx => ?_⟩
  show x ∈ kernelCongruenceSubgroup K 𝔪 χ
  unfold kernelCongruenceSubgroup
  simp only [Subgroup.mem_comap]
  have hq : (QuotientGroup.mk' (RayGroup K 𝔪)) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx
  rw [hq]
  exact (MonoidHom.ker χ).one_mem

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

noncomputable instance instFintypePrimitiveCharsContaining (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    [𝒞.FiniteIndex] :
    Fintype (PrimitiveCharsContaining K 𝔪 𝒞) := by
  unfold PrimitiveCharsContaining
  haveI : Finite (FracIdealsCoprime K 𝔪 ⧸ 𝒞) := Subgroup.finite_quotient_of_finiteIndex

  exact Fintype.ofFinite _

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

instance instDecidableIsPrincipalPrimitive (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (χ : PrimitiveCharsContaining K 𝔪 𝒞) :
    Decidable (isPrincipalPrimitive K 𝔪 𝒞 χ) := by
  unfold isPrincipalPrimitive IsRayClassCharacterPrincipal
  exact Classical.dec _

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

theorem extensionNormSubgroup_isCong (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    IsCongruenceSubgroup K (extensionAdmissibleModulus K L)
      (extensionNormSubgroup K L) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq (fun _ => by simp)
  haveI : FiniteDimensional ℚ L := Module.Finite.trans K L
  haveI : NumberField L := NumberField.mk
  exact ⟨rayGroup_le_normGroup K L (extensionAdmissibleModulus K L)⟩

noncomputable def extensionConductor (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Modulus K :=
  conductorOfCongruenceSubgroup K
    (extensionAdmissibleModulus K L)
    (extensionNormSubgroup K L)
    (extensionNormSubgroup_isCong K L)

def IsUnramifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
    𝔔.LiesOver 𝔭.asIdeal →
    Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) 𝔔

def IsTamelyRamifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
    𝔔.LiesOver 𝔭.asIdeal →
      ¬ (ringChar (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) ∣
          Ideal.ramificationIdx 𝔭.asIdeal 𝔔)

def IsWildlyRamifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∃ (𝔔 : Ideal (NumberField.RingOfIntegers L)) (_ : 𝔔.IsPrime),
    𝔔.LiesOver 𝔭.asIdeal ∧
      ringChar (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) ∣
        Ideal.ramificationIdx 𝔭.asIdeal 𝔔

def IsTotallyRamifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
    𝔔.LiesOver 𝔭.asIdeal →
      Ideal.inertiaDeg 𝔭.asIdeal 𝔔 = 1

def IsTotallyTamelyRamified (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  IsTotallyRamifiedIn K L 𝔭 ∧ IsTamelyRamifiedIn K L 𝔭

def IsTotallyWildlyRamified (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  IsTotallyRamifiedIn K L 𝔭 ∧
    ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
      𝔔.LiesOver 𝔭.asIdeal →
        ∃ k : ℕ, Ideal.ramificationIdx 𝔭.asIdeal 𝔔 =
          (ringChar (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal)) ^ k

noncomputable def NormGroup (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Modulus K) : Subgroup (FracIdealsCoprime K 𝔪) :=
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  letI : FiniteDimensional ℚ L := FiniteDimensional.trans ℚ K L
  letI : NumberField L := NumberField.mk

  RayClassField.NormGroup K L 𝔪

noncomputable def choosePrimeOverHOS (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prime' L :=
  ⟨choosePrimeOver K L 𝔭, choosePrimeOver_isPrime K L 𝔭, choosePrimeOver_ne_bot K L 𝔭⟩

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
attribute [instance] GlobalArtinMap.instPreorder
  GlobalArtinMap.instFintype
  GlobalArtinMap.instCommGroup
  GlobalArtinMap.galAb_group
  GlobalArtinMap.galAb_topologicalSpace
  GlobalArtinMap.galAb_topologicalGroup
  GlobalArtinMap.galAb_compactSpace

namespace GlobalArtinMap
end GlobalArtinMap

theorem theorem_28_4_principal_in_ker {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) :
    principalIdeles K ≤ MonoidHom.ker θ.artinHom :=
  θ.principalInKer

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

structure GlobalArtinFunctoriality
    (θK : GlobalArtinMap K) (θL : GlobalArtinMap L) where
  transfer : θL.GalAb →* θK.GalAb
  transfer_continuous : Continuous transfer
  artinMap_comm : ∀ (a : IdeleGroup L),
    θK.artinHom (ideleNorm K L a) = transfer (θL.artinHom a)

end Functoriality

section ArtinMapGaloisCorrespondence

open Ideles

variable {K : Type*} [Field K] [NumberField K]
