/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Derivation.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.CotangentLocal.Part3
open IsLocalRing


namespace CotangentDual

variable {R : Type*} [CommRing R] [IsLocalRing R]

variable {k : Type*} [Field k] [Algebra k R] [Algebra R k]

variable [IsScalarTower k R k]

noncomputable def derivToDual
    (hφ : Function.Surjective (algebraMap R k))
    (D : Derivation k R k) : Module.Dual k (CotangentSpace R) :=
  Ideal.Cotangent.lift (derivRestrict D) (derivRestrict_vanishes hφ D)

noncomputable def dualToDeriv
    (hφ : Function.Surjective (algebraMap R k))
    (ψ : Module.Dual k (CotangentSpace R)) : Derivation k R k where
  toLinearMap := {
    toFun := fun r => ψ ((maximalIdeal R).toCotangent (projMaxIdeal hφ r))
    map_add' := fun x y => by rw [projMaxIdeal_add, map_add, map_add]
    map_smul' := fun c x => by
      simp only [RingHom.id_apply]
      rw [projMaxIdeal_smul, LinearMap.map_smul_of_tower, map_smul]
  }
  map_one_eq_zero' := by
    show ψ ((maximalIdeal R).toCotangent (projMaxIdeal hφ 1)) = 0
    rw [projMaxIdeal_one, map_zero, map_zero]
  leibniz' := fun a b => by
    show ψ ((maximalIdeal R).toCotangent (projMaxIdeal hφ (a * b))) =
      a • ψ ((maximalIdeal R).toCotangent (projMaxIdeal hφ b)) +
      b • ψ ((maximalIdeal R).toCotangent (projMaxIdeal hφ a))
    rw [projCotangent_leibniz hφ, map_add]
    simp_rw [algebraMap_smul R]; simp_rw [map_smul]
    simp only [Algebra.algebraMap_self_apply, Algebra.smul_def]

noncomputable def derivToDualLinear
    (hφ : Function.Surjective (algebraMap R k)) :
    Derivation k R k →ₗ[k] Module.Dual k (CotangentSpace R) where
  toFun := derivToDual hφ
  map_add' D₁ D₂ := by
    ext v; induction v using Quotient.inductionOn with
    | h m =>
      show (derivToDual hφ (D₁ + D₂)) ((maximalIdeal R).toCotangent m) =
        ((derivToDual hφ D₁) + (derivToDual hφ D₂)) ((maximalIdeal R).toCotangent m)
      simp only [derivToDual, Ideal.Cotangent.lift_toCotangent, derivRestrict,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]; rfl
  map_smul' c D := by
    ext v; induction v using Quotient.inductionOn with
    | h m =>
      show (derivToDual hφ (c • D)) ((maximalIdeal R).toCotangent m) =
        (c • (derivToDual hφ D)) ((maximalIdeal R).toCotangent m)
      simp only [derivToDual, Ideal.Cotangent.lift_toCotangent, derivRestrict,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul]; rfl

noncomputable def dualToDerivLinear
    (hφ : Function.Surjective (algebraMap R k)) :
    Module.Dual k (CotangentSpace R) →ₗ[k] Derivation k R k where
  toFun := dualToDeriv hφ
  map_add' ψ₁ ψ₂ := by ext r; simp [dualToDeriv]
  map_smul' c ψ := by ext r; simp [dualToDeriv]

noncomputable def cotangentDualEquivDerivation
    (hφ : Function.Surjective (algebraMap R k)) :
    Module.Dual k (CotangentSpace R) ≃ₗ[k] Derivation k R k :=
  LinearEquiv.ofLinear (dualToDerivLinear hφ) (derivToDualLinear hφ)
    (by
      ext D a
      show (derivToDual hφ D) ((maximalIdeal R).toCotangent (projMaxIdeal hφ a)) = D a
      show D (projMaxIdeal hφ a).val = D a
      simp only [projMaxIdeal, Subtype.coe_mk, map_sub, Derivation.map_algebraMap, sub_zero])
    (by
      ext ψ v
      induction v using Quotient.inductionOn with
      | h m =>
        show (derivToDual hφ (dualToDeriv hφ ψ)) ((maximalIdeal R).toCotangent m) =
          ψ ((maximalIdeal R).toCotangent m)
        simp only [derivToDual, Ideal.Cotangent.lift_toCotangent, derivRestrict,
          LinearMap.coe_mk, AddHom.coe_mk]
        show ψ ((maximalIdeal R).toCotangent (projMaxIdeal hφ m.val)) =
          ψ ((maximalIdeal R).toCotangent m)
        rw [projMaxIdeal_of_mem])

end CotangentDual
