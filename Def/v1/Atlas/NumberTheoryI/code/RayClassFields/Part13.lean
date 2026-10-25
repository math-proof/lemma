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
import Theorem.v1.Atlas.NumberTheoryI.code.RayClassFields.Part7


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

def UnitsCongruent_subgroup' (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Subgroup Kˣ where
  carrier := {α |

    (∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
      v.valuation K (α : K) = 1) ∧

    (∀ v : FinitePlace K, 𝔪 (Place.finite v) ≠ 0 →
      v.valuation K ((α : K) - 1) ≤
        ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ)))) ∧

    (∀ w : NumberField.InfinitePlace K, 𝔪 (Place.infinite w) ≠ 0 →
      0 < (w.embedding (α : K)).re)}
  one_mem' := by
    refine ⟨fun v _ => Valuation.map_one _, fun v _ => ?_, fun w _ => ?_⟩
    · simp only [Units.val_one, sub_self, map_zero]
      exact WithZero.zero_le _
    · simp [map_one, Complex.one_re]
  mul_mem' := by
    intro a b ⟨ha_cop, ha_cong, ha_sign⟩ ⟨hb_cop, hb_cong, hb_sign⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      simp [map_mul, ha_cop v hv, hb_cop v hv]
    · intro v hv
      have key : ((a * b : Kˣ) : K) - 1 = (a : K) * ((b : K) - 1) + ((a : K) - 1) := by
        simp only [Units.val_mul]; ring
      rw [key]
      calc v.valuation K ((a : K) * ((b : K) - 1) + ((a : K) - 1))
          ≤ max (v.valuation K ((a : K) * ((b : K) - 1))) (v.valuation K ((a : K) - 1)) :=
            Valuation.map_add _ _ _
        _ ≤ max (↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ))))
              (↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ)))) := by
            apply max_le_max
            · rw [map_mul, ha_cop v hv, one_mul]; exact hb_cong v hv
            · exact ha_cong v hv
        _ = _ := max_self _
    · intro w hw
      have hw_real : w.IsReal := by
        by_contra h
        exact hw (𝔪.complex_zero w (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp h))
      rw [Units.val_mul, map_mul, Complex.mul_re]
      rw [embedding_im_zero hw_real, embedding_im_zero hw_real]
      simp only [mul_zero, sub_zero]
      exact mul_pos (ha_sign w hw) (hb_sign w hw)
  inv_mem' := by
    intro a ⟨ha_cop, ha_cong, ha_sign⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      simp [map_inv₀, ha_cop v hv]
    · intro v hv
      have key : ((a⁻¹ : Kˣ) : K) - 1 = -((a : K) - 1) * ((a⁻¹ : Kˣ) : K) := by
        simp only [Units.val_inv_eq_inv_val]; field_simp; ring
      rw [key, map_mul, Valuation.map_neg]
      have : v.valuation K ((a⁻¹ : Kˣ) : K) = 1 := by
        rw [Units.val_inv_eq_inv_val, map_inv₀, ha_cop v hv, inv_one]
      rw [this, mul_one]
      exact ha_cong v hv
    · intro w hw
      have hw_real : w.IsReal := by
        by_contra h
        exact hw (𝔪.complex_zero w (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp h))
      rw [Units.val_inv_eq_inv_val, map_inv₀, Complex.inv_re]
      have him : (w.embedding (a : K)).im = 0 := embedding_im_zero hw_real _
      have hnsq : Complex.normSq (w.embedding (a : K)) = (w.embedding (a : K)).re ^ 2 := by
        rw [Complex.normSq_apply, him, mul_zero, add_zero, sq]
      rw [hnsq]
      exact div_pos (ha_sign w hw) (sq_pos_of_pos (ha_sign w hw))

def UnitsCongruent (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Type u :=
  UnitsCongruent_subgroup' K 𝔪

def UnitsCongruent_in_UnitsCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Subgroup (UnitsCoprime_subgroup' K 𝔪) :=
  (UnitsCongruent_subgroup' K 𝔪).subgroupOf (UnitsCoprime_subgroup' K 𝔪)

def QuotientUnits (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Type u :=
  (UnitsCoprime_subgroup' K 𝔪) ⧸ (UnitsCongruent_in_UnitsCoprime K 𝔪)

end RayClassField
end
