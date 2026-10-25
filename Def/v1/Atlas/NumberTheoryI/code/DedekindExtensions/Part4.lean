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
import Theorem.v1.Atlas.NumberTheoryI.code.DedekindExtensions.Part3
open Module


noncomputable section

section DualInvertibleFractionalIdeal

open scoped nonZeroDivisors

variable (A : Type*) [CommRing A] [IsDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

def nonzeroElemOfFractionalIdeal (M : FractionalIdeal A⁰ K) (hM : M ≠ 0) :
    {m : (↑M : Submodule A K) // (m : K) ≠ 0} :=
  let h := FractionalIdeal.exists_ne_zero_mem_isInteger hM
  let x := h.choose
  let hx := h.choose_spec
  ⟨⟨algebraMap A K x, hx.2⟩,
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hx.1⟩

def dualEquivInverse
    (M : FractionalIdeal A⁰ K) (hM : IsUnit M) :
    Module.Dual A (↑M : Submodule A K) ≃ₗ[A] (↑(M⁻¹) : Submodule A K) :=
  let hMne : M ≠ 0 := by intro h; rw [h] at hM; exact not_isUnit_zero hM
  let ⟨m₀, hm₀⟩ := nonzeroElemOfFractionalIdeal A K M hMne
  (dualEquivColonSubmodule A K (↑M) m₀ hm₀).trans
    (LinearEquiv.ofEq _ _ (colonSubmodule_eq_coe_inv A K M hMne))

def doubleDualEquiv
    (M : FractionalIdeal A⁰ K) (hM : IsUnit M) :
    Module.Dual A (Module.Dual A (↑M : Submodule A K)) ≃ₗ[A] (↑M : Submodule A K) :=
  let hMinvU : IsUnit M⁻¹ := by
    rw [isUnit_iff_exists_inv]
    exact ⟨M, by rw [mul_comm]; exact (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mpr hM⟩
  let hMinv_inv_eq : M⁻¹⁻¹ = M := by
    rw [← FractionalIdeal.right_inverse_eq K M⁻¹ M]
    rw [mul_comm]
    exact (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mpr hM

  let e₁ := dualEquivInverse A K M hM

  let e₂ := e₁.dualMap.symm

  let e₃ := dualEquivInverse A K M⁻¹ hMinvU

  let e₄ := LinearEquiv.ofEq _ _ (congrArg FractionalIdeal.coeToSubmodule hMinv_inv_eq)
  e₂.trans (e₃.trans e₄)

end DualInvertibleFractionalIdeal


section DualBasis

variable {A : Type*} [CommRing A]

variable {M : Type*} [AddCommGroup M] [Module A M]

variable {n : ℕ}

def perfPairingDualBasis (p : M →ₗ[A] M →ₗ[A] A) [p.IsPerfPair] (b : Basis ι A M) :
    Basis ι A M :=
  b.dualBasis.map p.toPerfPair.symm

end DualBasis
end
