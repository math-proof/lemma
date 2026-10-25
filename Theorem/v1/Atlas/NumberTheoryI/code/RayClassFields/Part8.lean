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
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part16


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

lemma Modulus.finitePartIdeal_ne_bot (𝔪 : @Modulus K _ _) :
    𝔪.finitePartIdeal ≠ ⊥ := by
  unfold Modulus.finitePartIdeal
  rw [ne_eq, ← Ideal.zero_eq_bot, ← ne_eq]
  exact Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ => by
    rw [ne_eq, Ideal.zero_eq_bot, ← ne_eq, ← Ideal.zero_eq_bot]
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact 𝔭.ne_bot))

theorem lemma_21_7_ideal_class_coprime_rep
    (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (𝔞 : Ideal A) (c : ClassGroup A) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ (I : nonZeroDivisors (Ideal A)),
      ClassGroup.mk0 I = c
      ∧ (∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum A,
        𝔭.asIdeal ∣ 𝔞 → ¬(𝔭.asIdeal ∣ (I : Ideal A))) := by

  obtain ⟨⟨J, hJ_mem⟩, hJ_class⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ_ne : J ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp hJ_mem

  have hle : J * 𝔞 ≤ J := Ideal.mul_le_right
  have hne : J * 𝔞 ≠ ⊥ := mul_ne_zero hJ_ne h𝔞
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
  have ha_le : Ideal.span {a} ≤ J := by rw [← ha]; exact le_sup_right
  obtain ⟨K, hK_eq⟩ := Ideal.dvd_iff_le.mpr ha_le

  have hK_coprime : K ⊔ 𝔞 = ⊤ := by
    rw [sup_comm]
    exact mul_left_cancel₀ hJ_ne
      (by rw [Ideal.mul_sup, Ideal.mul_top, ← hK_eq, ha])
  by_cases hK_ne : K = ⊥
  ·
    have h𝔞_top : 𝔞 = ⊤ := by rw [← hK_coprime, hK_ne, bot_sup_eq]
    obtain ⟨⟨K', hK'_mem⟩, hK'_class⟩ := ClassGroup.mk0_surjective c
    exact ⟨⟨K', hK'_mem⟩, hK'_class, fun 𝔭 h𝔭 _ => by
      rw [h𝔞_top] at h𝔭
      exact 𝔭.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp h𝔭))⟩
  ·
    have hJK_ne : J * K ≠ ⊥ := mul_ne_zero hJ_ne hK_ne

    have h1 : ClassGroup.mk0
        ⟨J * K, mem_nonZeroDivisors_iff_ne_zero.mpr hJK_ne⟩ = 1 := by
      rw [ClassGroup.mk0_eq_one_iff]
      rw [← hK_eq]; exact ⟨⟨a, rfl⟩⟩

    have h2 : ClassGroup.mk0
        ⟨J * K, mem_nonZeroDivisors_iff_ne_zero.mpr hJK_ne⟩ =
      ClassGroup.mk0 ⟨J, hJ_mem⟩ *
        ClassGroup.mk0
          ⟨K, mem_nonZeroDivisors_iff_ne_zero.mpr hK_ne⟩ := by
      rw [← MonoidHom.map_mul]; congr 1
    rw [h2, hJ_class] at h1

    exact ⟨⟨K, mem_nonZeroDivisors_iff_ne_zero.mpr hK_ne⟩,
      (eq_of_inv_mul_eq_one h1).symm,


      fun 𝔭 h𝔭𝔞 h𝔭K => by
        have : K ⊔ 𝔞 ≤ 𝔭.asIdeal :=
          sup_le (Ideal.dvd_iff_le.mp h𝔭K) (Ideal.dvd_iff_le.mp h𝔭𝔞)
        rw [hK_coprime] at this
        exact 𝔭.isPrime.ne_top (top_le_iff.mp this)⟩

end RayClassField
end
