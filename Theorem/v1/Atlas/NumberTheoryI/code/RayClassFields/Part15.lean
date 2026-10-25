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
import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part23


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

theorem coprime_rep_well_def (𝔪 : @Modulus K _ _)
    {a b c d : NumberField.RingOfIntegers K}
    (ha : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal a))
    (hb : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal b))
    (hc : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal c))
    (hd : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal d))
    (hab : algebraMap (NumberField.RingOfIntegers K) K a /
             algebraMap (NumberField.RingOfIntegers K) K b =
           algebraMap (NumberField.RingOfIntegers K) K c /
             algebraMap (NumberField.RingOfIntegers K) K d) :
    ha.unit * hb.unit⁻¹ = hc.unit * hd.unit⁻¹ := by

  by_cases htriv : Subsingleton (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)
  · haveI := htriv
    exact Subsingleton.elim _ _
  · rw [not_subsingleton_iff_nontrivial] at htriv
    haveI := htriv

    have hb_ne : algebraMap (NumberField.RingOfIntegers K) K b ≠ 0 := by
      intro heq
      exact hb.ne_zero (show Ideal.Quotient.mk 𝔪.finitePartIdeal b = 0 from by
        have : b = 0 := IsFractionRing.injective _ K (by rwa [map_zero])
        rw [this, map_zero])
    have hd_ne : algebraMap (NumberField.RingOfIntegers K) K d ≠ 0 := by
      intro heq
      exact hd.ne_zero (show Ideal.Quotient.mk 𝔪.finitePartIdeal d = 0 from by
        have : d = 0 := IsFractionRing.injective _ K (by rwa [map_zero])
        rw [this, map_zero])

    have h_integral : a * d = b * c := IsFractionRing.injective _ K (by
      simp only [map_mul]
      have h := (div_eq_div_iff hb_ne hd_ne).mp hab
      rw [mul_comm (algebraMap (NumberField.RingOfIntegers K) K c)
          (algebraMap (NumberField.RingOfIntegers K) K b)] at h
      exact h)

    have h_quot : Ideal.Quotient.mk 𝔪.finitePartIdeal a *
                  Ideal.Quotient.mk 𝔪.finitePartIdeal d =
                  Ideal.Quotient.mk 𝔪.finitePartIdeal b *
                  Ideal.Quotient.mk 𝔪.finitePartIdeal c := by
      rw [← map_mul, ← map_mul, h_integral]

    have key : ha.unit * hd.unit = hb.unit * hc.unit := by
      ext; simp [IsUnit.unit_spec, h_quot]

    exact mul_right_cancel (b := hb.unit * hd.unit) (by
      calc ha.unit * hb.unit⁻¹ * (hb.unit * hd.unit)
          = ha.unit * (hb.unit⁻¹ * hb.unit) * hd.unit := by simp only [mul_assoc]
        _ = ha.unit * hd.unit := by simp
        _ = hb.unit * hc.unit := key
        _ = hc.unit * hb.unit := mul_comm _ _
        _ = hc.unit * (hd.unit⁻¹ * hd.unit) * hb.unit := by simp
        _ = hc.unit * hd.unit⁻¹ * (hd.unit * hb.unit) := by simp only [mul_assoc]
        _ = hc.unit * hd.unit⁻¹ * (hb.unit * hd.unit) := by rw [mul_comm hd.unit hb.unit])

end RayClassField
end
