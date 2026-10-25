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
import Theorem.v1.Atlas.NumberTheoryI.code.RayClassFields.Part15


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

noncomputable def finitePartMapHom (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    UnitsCoprime_subgroup' K 𝔪 →*
      (NumberField.RingOfIntegers K ⧸ 𝔪.finitePartIdeal)ˣ where
  toFun := finitePartMapFn K 𝔪
  map_one' := by
    show finitePartMapFn K 𝔪 1 = 1
    simp only [finitePartMapFn]
    have h := coprime_rep_exists 𝔪 (1 : UnitsCoprime_subgroup' K 𝔪)
    have ha := h.choose_spec.choose_spec.1
    have hb := h.choose_spec.choose_spec.2.1
    have heq' := h.choose_spec.choose_spec.2.2
    have h1u : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal (1 : 𝓞 K)) := isUnit_one

    simp only [Subgroup.coe_one, Units.val_one] at heq'


    have := coprime_rep_well_def 𝔪 ha hb h1u h1u (by rw [map_one, div_one]; exact heq')
    rw [this]
    simp
  map_mul' := fun x y => by
    show finitePartMapFn K 𝔪 (x * y) = finitePartMapFn K 𝔪 x * finitePartMapFn K 𝔪 y
    simp only [finitePartMapFn]

    have hx := coprime_rep_exists 𝔪 x
    have hy := coprime_rep_exists 𝔪 y
    have hxy := coprime_rep_exists 𝔪 (x * y)
    have hax := hx.choose_spec.choose_spec.1
    have hbx := hx.choose_spec.choose_spec.2.1
    have heqx := hx.choose_spec.choose_spec.2.2
    have hay := hy.choose_spec.choose_spec.1
    have hby := hy.choose_spec.choose_spec.2.1
    have heqy := hy.choose_spec.choose_spec.2.2
    have haxy := hxy.choose_spec.choose_spec.1
    have hbxy := hxy.choose_spec.choose_spec.2.1
    have heqxy := hxy.choose_spec.choose_spec.2.2

    have haxay : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal
        (hx.choose * hy.choose)) := by
      rw [map_mul]; exact hax.mul hay
    have hbxby : IsUnit (Ideal.Quotient.mk 𝔪.finitePartIdeal
        (hx.choose_spec.choose * hy.choose_spec.choose)) := by
      rw [map_mul]; exact hbx.mul hby
    simp only [Subgroup.coe_mul, Units.val_mul] at heqxy
    have hprod : algebraMap (𝓞 K) K (hx.choose * hy.choose) /
        algebraMap (𝓞 K) K (hx.choose_spec.choose * hy.choose_spec.choose) =
        ((x : Kˣ) : K) * ((y : Kˣ) : K) := by
      trans (algebraMap (𝓞 K) K hx.choose / algebraMap (𝓞 K) K hx.choose_spec.choose *
             (algebraMap (𝓞 K) K hy.choose / algebraMap (𝓞 K) K hy.choose_spec.choose))
      · simp only [map_mul, div_mul_div_comm]
      · rw [heqx, heqy]
    have hwd := coprime_rep_well_def 𝔪 haxy hbxy haxay hbxby
      (by rw [hprod]; exact heqxy)
    have key1 : haxay.unit = hax.unit * hay.unit := by
      ext; simp only [Units.val_mul, IsUnit.unit_spec, map_mul]
    have key2 : hbxby.unit = hbx.unit * hby.unit := by
      ext; simp only [Units.val_mul, IsUnit.unit_spec, map_mul]
    rw [hwd, key1, key2, mul_inv_rev]
    calc hax.unit * hay.unit * (hby.unit⁻¹ * hbx.unit⁻¹)
        = hax.unit * (hay.unit * hby.unit⁻¹) * hbx.unit⁻¹ := by
          simp only [mul_assoc]
      _ = hax.unit * hbx.unit⁻¹ * (hay.unit * hby.unit⁻¹) :=
          mul_right_comm _ _ _

end RayClassField
end
