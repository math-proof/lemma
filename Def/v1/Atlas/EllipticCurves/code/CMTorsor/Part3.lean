/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.ClassGroup
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Structure.v1.Atlas.EllipticCurves.code.CMTorsor.Part2


namespace FieldNormTrace

section Quadratic

variable {D : ℤ}

namespace FractionalOIdeal

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]

open FractionalIdeal

/-- The discriminant `t² - 4n` of an imaginary quadratic order. -/
def ImaginaryQuadraticOrder.discriminant (𝒪 : ImaginaryQuadraticOrder) : ℤ :=
  𝒪.t ^ 2 - 4 * 𝒪.n

/-- Two imaginary quadratic orders agree (define the same order) when they have the same
discriminant and the same trace parity. -/
def ImaginaryQuadraticOrder.SameOrder (𝒪₁ 𝒪₂ : ImaginaryQuadraticOrder) : Prop :=
  𝒪₁.discriminant = 𝒪₂.discriminant ∧ 𝒪₁.t % 2 = 𝒪₂.t % 2

/-- Construct an `ImaginaryQuadraticOrder` of discriminant `D = u² · D_K` from the
decomposition `dec` into a conductor `u` and a fundamental discriminant `D_K`. -/
def orderFromDecomposition {D : ℤ}
    (dec : ImaginaryQuadraticDiscriminantDecomposition D) :
    ImaginaryQuadraticOrder where


  t := if dec.D_K % 4 = 0 then 0 else dec.u


  n := if dec.D_K % 4 = 0 then
    -(dec.u ^ 2 * (dec.D_K / 4))
  else
    -(dec.u ^ 2 * ((dec.D_K - 1) / 4))
  hdisc_neg := by
    have hu_sq_pos : dec.u ^ 2 ≥ 1 := by nlinarith [dec.hu]
    rcases dec.hD_K.1.2 with h0 | h1
    · simp only [h0, ↑reduceIte]
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
      have hk_neg : k < 0 := by nlinarith [dec.hD_K.1.1]
      have : dec.D_K / 4 = k := by omega
      rw [this]; nlinarith
    · have h0f : ¬(dec.D_K % 4 = 0) := by omega
      simp only [h0f, ↑reduceIte]
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (dec.D_K - 1) % 4 = 0 by omega)
      have hm_neg : m < 0 := by nlinarith [dec.hD_K.1.1]
      have : (dec.D_K - 1) / 4 = m := by omega
      rw [this]; nlinarith
  hdisc_mod := by
    rcases dec.hD_K.1.2 with h0 | h1
    · simp only [h0, ↑reduceIte]; left; omega
    · have h0f : ¬(dec.D_K % 4 = 0) := by omega
      simp only [h0f, ↑reduceIte]
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (dec.D_K - 1) % 4 = 0 by omega)
      have hm_eq : (dec.D_K - 1) / 4 = m := by omega
      rw [hm_eq]
      rcases (show dec.u % 2 = 0 ∨ dec.u % 2 = 1 by omega) with hu | hu
      · left
        obtain ⟨j, hj⟩ := Int.dvd_of_emod_eq_zero hu
        have : dec.u ^ 2 - 4 * -(dec.u ^ 2 * m) = dec.u ^ 2 * (4 * m + 1) := by ring
        rw [this, hj]; ring_nf; omega
      · right
        obtain ⟨j, hj⟩ := Int.dvd_of_emod_eq_zero (show (dec.u - 1) % 2 = 0 by omega)
        have hu_eq : dec.u = 2 * j + 1 := by omega
        have : dec.u ^ 2 - 4 * -(dec.u ^ 2 * m) = dec.u ^ 2 * (4 * m + 1) := by ring
        rw [this, hu_eq]; ring_nf; omega

/-- The maximal order of an imaginary quadratic field with fundamental discriminant `D_K`,
constructed as an `ImaginaryQuadraticOrder`. -/
def maximalOrder (D_K : ℤ) (hfund : IsFundamentalImaginaryQuadraticDiscriminant D_K) :
    ImaginaryQuadraticOrder where
  t := if D_K % 4 = 0 then 0 else 1
  n := if D_K % 4 = 0 then -(D_K / 4) else -((D_K - 1) / 4)
  hdisc_neg := by
    rcases hfund.1.2 with h0 | h1
    · simp only [h0, ↑reduceIte]
      obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h0
      have : D_K / 4 = k := by omega
      rw [this]; nlinarith [hfund.1.1]
    · have h0f : ¬(D_K % 4 = 0) := by omega
      simp only [h0f, ↑reduceIte]
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (D_K - 1) % 4 = 0 by omega)
      have : (D_K - 1) / 4 = m := by omega
      rw [this]; nlinarith [hfund.1.1]
  hdisc_mod := by
    rcases hfund.1.2 with h0 | h1
    · simp only [h0, ↑reduceIte]; left; omega
    · have h0f : ¬(D_K % 4 = 0) := by omega
      simp only [h0f, ↑reduceIte]; right
      obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero (show (D_K - 1) % 4 = 0 by omega)
      have : (D_K - 1) / 4 = m := by omega
      rw [this]; omega

/-- `𝒪` is a suborder of `𝒪_K` with index `u` if its discriminant is `u²` times that of
`𝒪_K` and the traces satisfy `𝒪.t = 2a + u · 𝒪_K.t` for some integer `a`. -/
def ImaginaryQuadraticOrder.IsSuborderOfIndex (𝒪 𝒪_K : ImaginaryQuadraticOrder) (u : ℤ) : Prop :=
  u ≥ 1 ∧ 𝒪.discriminant = u ^ 2 * 𝒪_K.discriminant ∧
  ∃ a : ℤ, 𝒪.t = 2 * a + u * 𝒪_K.t

/-- The order (multiplier ring) of a fractional ideal `I` in `K`: the set of `x : K` such
that `x · I ⊆ I`. -/
def idealOrder (I : FractionalIdeal R⁰ K) : Set K :=
  {x : K | ∀ y ∈ (I : Submodule R K), x * y ∈ (I : Submodule R K)}

/-- A fractional ideal `I` is *proper* if its order equals the image of `R` in `K`, i.e.
its multiplier ring is exactly `R` itself. -/
def IsProper (I : FractionalIdeal R⁰ K) : Prop :=
  idealOrder I = Set.range (algebraMap R K)

/-- The canonical `ℤ`-linear equivalence `ℤ√d ≃ₗ[ℤ] (Fin 2 → ℤ)` sending `α` to
`![α.re, α.im]`. Exhibits `ℤ√d` as a free `ℤ`-module of rank 2. -/
noncomputable def zsqrtdLinearEquivFin2 (d : ℤ) : (ℤ√d) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![x.re, x.im]
  invFun v := ⟨v 0, v 1⟩
  map_add' x y := by ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  map_smul' r x := by ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  left_inv x := by ext <;> simp
  right_inv v := by ext i; fin_cases i <;> simp

end FractionalOIdeal
end Quadratic
end FieldNormTrace
