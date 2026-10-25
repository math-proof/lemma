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
import Def.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part4


noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

section ArtinSymbol

universe v

variable (K : Type v) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

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

end ArtinSymbol
end
