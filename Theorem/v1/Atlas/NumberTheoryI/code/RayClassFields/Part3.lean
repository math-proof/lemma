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
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part8


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

theorem primeAsUnitFracIdeal_coprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝔭 : FinitePlace K) (h𝔭 : 𝔪 (Place.finite 𝔭) = 0) :
    (primeAsUnitFracIdeal K 𝔭 : (FracIdeal K)ˣ) ∈ FracIdealsCoprime_subgroup K 𝔪 := by
  intro v hv

  have hne : 𝔭 ≠ v := by intro heq; rw [heq] at h𝔭; exact hv h𝔭

  have hnotsubset : ¬ (𝔭.asIdeal ≤ v.asIdeal) := by
    intro h
    exact hne (IsDedekindDomain.HeightOneSpectrum.ext_iff.mpr
      (𝔭.isMaximal.eq_of_le v.isPrime.ne_top h))

  obtain ⟨r, hr𝔭, hrv⟩ := Set.not_subset.mp hnotsubset

  have hval : (primeAsUnitFracIdeal K 𝔭 : FracIdeal K) = 𝔭.asIdeal := by
    simp [primeAsUnitFracIdeal, IsUnit.unit]
  constructor
  ·

    refine ⟨algebraMap _ K r, ?_, ?_⟩
    · rw [hval]
      exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨r, hr𝔭, rfl⟩
    · rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v r).mpr hrv
  ·

    unfold HasTrivialValuation
    simp only [Units.val_inv_eq_inv_val]
    refine ⟨1, ?_, Valuation.map_one _⟩
    rw [hval]
    have hne_zero : (𝔭.asIdeal : FracIdeal K) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.mpr 𝔭.ne_bot
    have hinv : 1⁻¹ ≤ (𝔭.asIdeal : FracIdeal K)⁻¹ :=
      FractionalIdeal.inv_anti_mono hne_zero one_ne_zero FractionalIdeal.coeIdeal_le_one
    simp only [inv_one] at hinv
    exact hinv (FractionalIdeal.one_mem_one _)

end RayClassField
end
