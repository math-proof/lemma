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
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part9


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

set_option maxHeartbeats 800000 in
lemma count_spanSingleton_eq_zero (K : Type u) [Field K] [NumberField K]
    (v : FinitePlace K) (x : K) (hx : x ≠ 0) (hv : v.valuation K x = 1) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton
      (nonZeroDivisors (NumberField.RingOfIntegers K)) x) = 0 := by
  set R := NumberField.RingOfIntegers K
  obtain ⟨⟨r, ⟨s, hs⟩⟩, hrsx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hs_ne : (s : R) ≠ 0 := nonZeroDivisors.ne_zero hs
  have halgs_ne : algebraMap R K s ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) hs
  have hx_eq : x = algebraMap R K r * (algebraMap R K s)⁻¹ := by
    have h1 := hrsx
    simp only at h1
    field_simp
    linear_combination h1
  have hr_ne : r ≠ 0 := by intro hr; exact hx (by rw [hx_eq, hr, map_zero, zero_mul])
  have hne : FractionalIdeal.spanSingleton (nonZeroDivisors R) x ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
  rw [FractionalIdeal.count_well_defined K v hne (by
    rw [hx_eq, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
        ← FractionalIdeal.coeIdeal_span_singleton]; ring)]
  simp only [sub_eq_zero]
  have hval_eq : v.intValuation r = v.intValuation s := by
    have : v.valuation K x = v.intValuation r * (v.intValuation s)⁻¹ := by
      rw [hx_eq, map_mul, map_inv₀,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
          IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    rw [this] at hv
    rwa [mul_inv_eq_one₀ (v.intValuation_ne_zero s hs_ne)] at hv
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_apply,
      IsDedekindDomain.HeightOneSpectrum.intValuation_apply] at hval_eq
  simp only [IsDedekindDomain.HeightOneSpectrum.intValuationDef,
             if_neg hr_ne, if_neg hs_ne] at hval_eq
  exact_mod_cast neg_injective (WithZero.exp_injective hval_eq)

set_option maxHeartbeats 800000 in
lemma count_eq_zero_of_isCoprimeTo (K : Type u) [Field K] [NumberField K]
    (I : (FracIdeal K)ˣ) (v : FinitePlace K)
    (h : FracIdeal.IsCoprimeTo I v) :
    FractionalIdeal.count K v (I : FracIdeal K) = 0 := by
  obtain ⟨⟨x, hx_mem, hx_val⟩, ⟨y, hy_mem, hy_val⟩⟩ := h
  have hx_ne : x ≠ 0 := by intro h0; simp [h0] at hx_val
  have hy_ne : y ≠ 0 := by intro h0; simp [h0] at hy_val
  have h1 : FractionalIdeal.count K v I.val ≤ 0 :=
    calc FractionalIdeal.count K v I.val
        ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ x) :=
          FractionalIdeal.count_mono K v
            (by rwa [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff])
            (FractionalIdeal.spanSingleton_le_iff_mem.mpr hx_mem)
      _ = 0 := count_spanSingleton_eq_zero K v x hx_ne hx_val
  have h2 : 0 ≤ FractionalIdeal.count K v I.val := by
    have hcnt_inv : FractionalIdeal.count K v (I⁻¹ : (FracIdeal K)ˣ).val ≤ 0 :=
      calc FractionalIdeal.count K v (I⁻¹ : (FracIdeal K)ˣ).val
          ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ y) :=
            FractionalIdeal.count_mono K v
              (by rwa [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff])
              (FractionalIdeal.spanSingleton_le_iff_mem.mpr hy_mem)
        _ = 0 := count_spanSingleton_eq_zero K v y hy_ne hy_val
    rw [show (I⁻¹ : (FracIdeal K)ˣ).val = I.val⁻¹ from Units.val_inv_eq_inv_val I,
        FractionalIdeal.count_inv] at hcnt_inv
    linarith
  linarith

theorem primeCoprime_val (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝔭 : FinitePlace K) (h𝔭 : 𝔪 (Place.finite 𝔭) = 0) :
    (primeCoprime K 𝔪 𝔭 h𝔭).val = primeAsUnitFracIdeal K 𝔭 := rfl

theorem primeAsUnitFracIdeal_val (K : Type u) [Field K] [NumberField K]
    (𝔭 : FinitePlace K) :
    (primeAsUnitFracIdeal K 𝔭 : FracIdeal K) = 𝔭.asIdeal := by
  simp [primeAsUnitFracIdeal, IsUnit.unit]

theorem fracIdealsCoprime_closure_primes (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    Subgroup.closure (primesCoprime K 𝔪) = ⊤ := by
  rw [eq_top_iff]
  intro ⟨I, hI⟩ _

  set f : FinitePlace K →₀ ℤ := Multiplicative.toAdd (fractionalIdeal_mulEquiv_finsupp K I) with hf_def

  have hsupp : ∀ v ∈ f.support, 𝔪 (Place.finite v) = 0 := by
    intro v hv
    by_contra hmv
    have : f v = 0 := by
      rw [hf_def, fractionalIdeal_mulEquiv_finsupp_apply]
      exact count_eq_zero_of_isCoprimeTo K I v (hI v hmv)
    exact (Finsupp.mem_support_iff.mp hv) this

  set S := Subgroup.closure (primesCoprime K 𝔪)


  suffices h : ⟨I, hI⟩ = f.support.attach.prod (fun ⟨v, hv⟩ =>
      (primeCoprime K 𝔪 v (hsupp v hv)) ^ (f v)) by
    rw [h]
    exact S.prod_mem (fun ⟨v, hv⟩ _ =>
      S.zpow_mem (Subgroup.subset_closure ⟨v, hsupp v hv, rfl⟩) (f v))

  have hI_eq : I = (fractionalIdeal_mulEquiv_finsupp K).symm (Multiplicative.ofAdd f) := by
    rw [hf_def]; simp only [ofAdd_toAdd, MulEquiv.symm_apply_apply]


  have hprod_units : I = ∏ v ∈ f.support, primeAsUnitFracIdeal K v ^ f v := by
    rw [hI_eq]
    ext
    rw [fractionalIdeal_mulEquiv_finsupp_symm_apply]
    simp only [Finsupp.prod, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      primeAsUnitFracIdeal_val]

  apply Subtype.ext

  change I = (FracIdealsCoprime_subgroup K 𝔪).subtype
    (∏ x ∈ f.support.attach, (fun ⟨v, hv⟩ => (primeCoprime K 𝔪 v (hsupp v hv)) ^ (f v)) x)
  rw [map_prod]

  simp only [Subgroup.coe_subtype]

  exact hprod_units.trans (Finset.prod_attach _ _).symm

end RayClassField
end
