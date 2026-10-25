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
import Theorem.v1.Atlas.NumberTheoryI.code.RayClassFields.Part6


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

instance choosePrimeOver_comap_isPrime
    (K : Type u) (L : Type u) (M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsGalois K L] [IsGalois K M]
    [IsScalarTower K L M]
    (𝔭 : FinitePlace K) :
    ((choosePrimeOver K M 𝔭).comap
      (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))).IsPrime :=
  Ideal.IsPrime.comap _

instance choosePrimeOver_comap_finite
    (K : Type u) (L : Type u) (M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsGalois K L] [IsGalois K M]
    [IsScalarTower K L M]
    (𝔭 : FinitePlace K) :
    Finite (NumberField.RingOfIntegers L ⧸
      (choosePrimeOver K M 𝔭).comap
        (algebraMap (NumberField.RingOfIntegers L) (NumberField.RingOfIntegers M))) :=
  Ideal.finiteQuotientOfFreeOfNeBot _ (choosePrimeOver_comap_ne_bot K L M 𝔭)

noncomputable instance galAutFaithfulSMulRingOfIntegers
    (K : Type u) (L : Type u)
    [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    FaithfulSMul (L ≃ₐ[K] L) (NumberField.RingOfIntegers L) where
  eq_of_smul_eq_smul {σ τ} h := by
    have key : ∀ (a : NumberField.RingOfIntegers L),
        (σ : L ≃ₐ[K] L) a.val = (τ : L ≃ₐ[K] L) a.val :=
      fun a => congrArg Subtype.val (h a)
    ext x
    obtain ⟨⟨a, ⟨b, hb⟩⟩, hx⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers L)) x
    simp only at hx
    have hx' : x * (b : L) = (a : L) := by convert hx using 1 <;> rfl
    have : σ x * σ (b : L) = τ x * τ (b : L) := by
      calc σ x * σ (b : L) = σ (x * (b : L)) := (map_mul σ x (b : L)).symm
        _ = σ (a : L) := by rw [hx']
        _ = τ (a : L) := key a
        _ = τ (x * (b : L)) := by rw [hx']
        _ = τ x * τ (b : L) := map_mul τ x (b : L)
    rw [key b] at this
    have hb_ne : (τ : L ≃ₐ[K] L) (b : L) ≠ 0 := by
      intro h0
      have : (b : L) = 0 := by
        rw [show (b : L) = τ.symm (τ (b : L)) from (τ.symm_apply_apply _).symm, h0, map_zero]
      have hb' := map_ne_zero_of_mem_nonZeroDivisors
        (algebraMap (NumberField.RingOfIntegers L) L) (IsFractionRing.injective _ _) hb
      rw [NumberField.RingOfIntegers.coe_eq_algebraMap] at this
      exact hb' this
    exact mul_right_cancel₀ hb_ne this

end RayClassField
end
