/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.NumberTheory.NumberField.Basic
import Def.v1.Atlas.NumberTheoryI.code.Pairings.Part2
import Theorem.v1.Atlas.NumberTheoryI.code.DedekindExtensions.Part2
open Module


noncomputable section

section DualColonSubmodule

variable (A : Type*) [CommRing A] [IsDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

noncomputable def dualToColonMap (M : Submodule A K) (m₀ : M) (hm₀ : (m₀ : K) ≠ 0) :
    Module.Dual A M →ₗ[A] colonSubmodule A K M where
  toFun f := ⟨algebraMap A K (f m₀) * (m₀ : K)⁻¹, by
    intro m hm
    rw [show algebraMap A K (f m₀) * (m₀ : K)⁻¹ * m =
          algebraMap A K (f m₀) * (m₀ : K)⁻¹ * (⟨m, hm⟩ : M) from rfl]
    rw [dual_apply_via_element A K M f m₀ hm₀ ⟨m, hm⟩]
    exact ⟨f ⟨m, hm⟩, rfl⟩⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    show algebraMap A K ((f + g) m₀) * (↑m₀)⁻¹ =
      algebraMap A K (f m₀) * (↑m₀)⁻¹ + algebraMap A K (g m₀) * (↑m₀)⁻¹
    simp only [LinearMap.add_apply, map_add, add_mul]
  map_smul' := by
    intro c f
    apply Subtype.ext
    simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def]
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, mul_assoc]

noncomputable def dualEquivColonSubmodule (M : Submodule A K) (m₀ : M) (hm₀ : (m₀ : K) ≠ 0) :
    Module.Dual A M ≃ₗ[A] colonSubmodule A K M :=
  LinearEquiv.ofLinear
    (dualToColonMap A K M m₀ hm₀)
    (colonToDualMap A K M)
    (by
      ext ⟨x, hx⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      show (dualToColonMap A K M m₀ hm₀ (colonToDualMap A K M ⟨x, hx⟩) : K) = x
      simp only [dualToColonMap, colonToDualMap, LinearMap.coe_mk, AddHom.coe_mk, colonToA_spec]
      rw [mul_assoc]
      rw [mul_inv_cancel₀ hm₀, mul_one])
    (by
      ext f m
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      simp only [dualToColonMap, colonToDualMap, LinearMap.coe_mk, AddHom.coe_mk]
      apply IsFractionRing.injective A K
      rw [colonToA_spec]
      exact dual_apply_via_element A K M f m₀ hm₀ m)

end DualColonSubmodule
end
