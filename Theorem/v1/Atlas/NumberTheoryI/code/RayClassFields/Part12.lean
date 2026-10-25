/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part20


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

lemma valuation_eq_one_of_spanSingleton_coprime'
    (v : FinitePlace K) (α : Kˣ)
    (h1 : HasTrivialValuation (toPrincipalIdeal (NumberField.RingOfIntegers K) K α) v)
    (h2 : HasTrivialValuation (toPrincipalIdeal (NumberField.RingOfIntegers K) K α)⁻¹ v) :
    v.valuation K (α : K) = 1 := by

  obtain ⟨x, hx_mem, hx_val⟩ : ∃ x ∈ FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) (α : K),
      v.valuation K x = 1 := by
    rwa [HasTrivialValuation, coe_toPrincipalIdeal] at h1
  obtain ⟨y, hy_mem, hy_val⟩ : ∃ x ∈ FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) ((α⁻¹ : Kˣ) : K),
      v.valuation K x = 1 := by
    have : HasTrivialValuation (toPrincipalIdeal (NumberField.RingOfIntegers K) K α⁻¹) v := by
      rwa [map_inv]
    rwa [HasTrivialValuation, coe_toPrincipalIdeal] at this
  rw [FractionalIdeal.mem_spanSingleton] at hx_mem hy_mem
  obtain ⟨r, hr⟩ := hx_mem
  obtain ⟨s, hs⟩ := hy_mem

  subst hr; subst hs
  simp only [Algebra.smul_def] at hx_val hy_val
  rw [map_mul] at hx_val hy_val
  have hr_le : v.valuation K (algebraMap _ K r) ≤ 1 := v.valuation_le_one r
  have hs_le : v.valuation K (algebraMap _ K s) ≤ 1 := v.valuation_le_one s
  have hαα : v.valuation K (α : K) * v.valuation K ((α⁻¹ : Kˣ) : K) = 1 := by
    rw [← map_mul, show (α : K) * ((α⁻¹ : Kˣ) : K) = 1 from by simp, map_one]
  apply le_antisymm
  · calc v.valuation K (α : K)
        = v.valuation K (α : K) * 1 := (mul_one _).symm
      _ = v.valuation K (α : K) * (v.valuation K (algebraMap _ K s) *
          v.valuation K ((α⁻¹ : Kˣ) : K)) := by rw [hy_val]
      _ = (v.valuation K (α : K) * v.valuation K ((α⁻¹ : Kˣ) : K)) *
          v.valuation K (algebraMap _ K s) := by
            rw [mul_assoc, mul_comm (v.valuation K (algebraMap _ K s))]
      _ = 1 * v.valuation K (algebraMap _ K s) := by rw [hαα]
      _ = v.valuation K (algebraMap _ K s) := one_mul _
      _ ≤ 1 := hs_le
  · calc (1 : WithZero (Multiplicative ℤ))
        = v.valuation K (algebraMap _ K r) * v.valuation K (α : K) := hx_val.symm
      _ ≤ 1 * v.valuation K (α : K) := by gcongr
      _ = v.valuation K (α : K) := one_mul _

theorem exactSeq_exact_at_ray_class (𝔪 : @Modulus K _ _) :
    MonoidHom.range (exactSeq_map3 𝔪) = MonoidHom.ker (exactSeq_map4 𝔪) := by
  ext ⟨I⟩
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  ·
    rintro ⟨⟨α⟩, hα⟩
    rw [← hα]
    show exactSeq_map4 𝔪 (exactSeq_map3 𝔪
      (Quot.mk (QuotientGroup.leftRel (UnitsCongruent_in_UnitsCoprime K 𝔪)) α)) = 1
    have key3 : (exactSeq_map3 𝔪)
        (Quot.mk (QuotientGroup.leftRel (UnitsCongruent_in_UnitsCoprime K 𝔪)) α) =
        ((QuotientGroup.mk' (RayGroup K 𝔪)).comp (principalIdealMap 𝔪)) α := by
      simp only [exactSeq_map3]
      erw [QuotientGroup.lift_mk']
    simp only [MonoidHom.comp_apply] at key3
    rw [key3]
    show (exactSeq_map4 𝔪)
      (QuotientGroup.mk' (RayGroup K 𝔪) (principalIdealMap 𝔪 α)) = 1
    simp only [exactSeq_map4]
    erw [QuotientGroup.lift_mk']
    simp only [MonoidHom.comp_apply]
    rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff]
    refine ⟨((α : Kˣ) : K), ?_⟩

    have := principalIdealMap_val 𝔪 α
    show ((FracIdealsCoprime_subgroup K 𝔪).subtype (principalIdealMap 𝔪 α) : FracIdeal K) = _
    simp only [Subgroup.coe_subtype]
    exact this
  ·
    intro h

    have h_unfold : (ClassGroup.mk (K := K) ((FracIdealsCoprime_subgroup K 𝔪).subtype I)) = 1 := by
      have key4 : (exactSeq_map4 𝔪)
          (Quot.mk (QuotientGroup.leftRel (RayGroup K 𝔪)) I) =
          (ClassGroup.mk.comp (FracIdealsCoprime_subgroup K 𝔪).subtype) I := by
        simp only [exactSeq_map4]
        erw [QuotientGroup.lift_mk']
      simp only [MonoidHom.comp_apply] at key4
      rw [← key4]; exact h

    rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff] at h_unfold
    obtain ⟨a, ha⟩ := h_unfold


    have ha_ne : a ≠ 0 := by
      intro ha_zero
      rw [ha_zero, FractionalIdeal.spanSingleton_zero] at ha
      simp only [Subgroup.coe_subtype] at ha
      exact Units.ne_zero I.val ha


    set α : Kˣ := Units.mk0 a ha_ne

    have hI_eq_span : (I.val : (FracIdeal K)ˣ).val =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (α : K) := by
      simp only [Subgroup.coe_subtype] at ha
      simp only [α, Units.mk0_val]
      exact ha
    have hI_eq_topi : I.val = toPrincipalIdeal (𝓞 K) K α := by
      apply Units.val_injective
      rw [coe_toPrincipalIdeal]
      exact hI_eq_span
    have hα_coprime : α ∈ UnitsCoprime_subgroup' K 𝔪 := by
      intro v hv
      have hI_cop := I.property v hv
      rw [hI_eq_topi] at hI_cop
      exact valuation_eq_one_of_spanSingleton_coprime' v α hI_cop.1 hI_cop.2

    set γ : UnitsCoprime_subgroup' K 𝔪 := ⟨α, hα_coprime⟩

    have hγ_eq : principalIdealMap 𝔪 γ = I := by
      apply Subtype.ext
      apply Units.val_injective
      simp only [principalIdealMap, MonoidHom.coe_mk, OneHom.coe_mk, coe_toPrincipalIdeal]
      exact hI_eq_span.symm

    refine ⟨Quot.mk _ γ, ?_⟩

    have key_map3 : (exactSeq_map3 𝔪)
        (Quot.mk (QuotientGroup.leftRel (UnitsCongruent_in_UnitsCoprime K 𝔪)) γ) =
        ((QuotientGroup.mk' (RayGroup K 𝔪)).comp (principalIdealMap 𝔪)) γ := by
      simp only [exactSeq_map3]
      erw [QuotientGroup.lift_mk']
    simp only [MonoidHom.comp_apply] at key_map3
    rw [key_map3, hγ_eq]
    rfl

theorem mk0_mem_FracIdealsCoprime_of_coprime (𝔪 : @Modulus K _ _)
    (I : nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)))
    (hI : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔭.asIdeal ∣ 𝔪.finitePartIdeal → ¬(𝔭.asIdeal ∣ (I : Ideal (NumberField.RingOfIntegers K)))) :
    FractionalIdeal.mk0 K I ∈ FracIdealsCoprime_subgroup K 𝔪 := by
  intro v hv
  constructor
  ·


    have hv_dvd : v.asIdeal ∣ 𝔪.finitePartIdeal := by
      simp only [Modulus.finitePartIdeal]
      apply dvd_trans (dvd_pow_self v.asIdeal (Nat.pos_of_ne_zero hv).ne')
      exact Finset.dvd_prod_of_mem _ (by
        simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
        exact hv)

    have hv_ndvd : ¬(v.asIdeal ∣ (I : Ideal (NumberField.RingOfIntegers K))) := hI v hv_dvd

    rw [Ideal.dvd_iff_le] at hv_ndvd
    obtain ⟨x, hxI, hxv⟩ := Set.not_subset.mp hv_ndvd

    refine ⟨algebraMap _ K x, ?_, ?_⟩
    · rw [FractionalIdeal.coe_mk0]
      exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨x, hxI, rfl⟩
    · rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr hxv
  ·

    refine ⟨1, ?_, Valuation.map_one _⟩
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.coe_mk0]
    have hI_ne : (I : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥ := by
      intro h; exact nonZeroDivisors.ne_zero I.2 (by rwa [Ideal.zero_eq_bot])
    exact one_mem_inv_coe_ideal hI_ne

lemma classGroup_mk_comp_subtype_surjective (𝔪 : @Modulus K _ _) :
    Function.Surjective (ClassGroup.mk.comp
      (FracIdealsCoprime_subgroup K 𝔪).subtype) := by
  intro c
  obtain ⟨I, hI_class, hI_coprime⟩ :=
    lemma_21_7_ideal_class_coprime_rep (NumberField.RingOfIntegers K)
      𝔪.finitePartIdeal c 𝔪.finitePartIdeal_ne_bot
  have hI_mem := mk0_mem_FracIdealsCoprime_of_coprime 𝔪 I hI_coprime
  exact ⟨⟨FractionalIdeal.mk0 K I, hI_mem⟩, by
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact (ClassGroup.mk_mk0 K I).trans hI_class⟩

theorem exactSeq_surjective (𝔪 : @Modulus K _ _) :
    Function.Surjective (exactSeq_map4 𝔪) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (classGroup_mk_comp_subtype_surjective 𝔪) _

lemma Modulus.infSupportFinset_isReal (𝔪 : @Modulus K _ _)
    {w : NumberField.InfinitePlace K} (hw : w ∈ 𝔪.infSupportFinset) : w.IsReal := by
  simp only [Modulus.infSupportFinset, Set.Finite.mem_toFinset, Set.mem_preimage,
    Set.mem_setOf_eq] at hw
  by_contra h
  exact hw (𝔪.complex_zero w (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp h))

omit [NumberField K] in
lemma embedding_re_ne_zero {w : NumberField.InfinitePlace K} (hw : w.IsReal) (a : Kˣ) :
    (w.embedding (a : K)).re ≠ 0 := by
  intro h
  have hne : w.embedding (a : K) ≠ 0 := by
    rw [map_ne_zero_iff _ (RingHom.injective w.embedding)]; exact Units.ne_zero a
  exact hne (Complex.ext h (embedding_im_zero hw _))

end RayClassField
end
