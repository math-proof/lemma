/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.CharP.Defs
import Def.v1.Atlas.EllipticCurves.code.ModularCurves.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ModularCurves
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import Def.v1.Atlas.EllipticCurves.code.Uniformization
import Def.v1.Atlas.EllipticCurves.code.ModularPolynomial.Part3
open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup Complex


noncomputable section

open ModularFunction

section ModularCurveX0Defs

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Matrix

open scoped MatrixGroups UpperHalfPlane

namespace ExtendedUpperHalfPlane

/-- The identity matrix acts trivially on the cusps. -/
theorem cuspAction_one : ∀ x, cuspAction 1 x = x := by
  intro x
  cases x with
  | top => simp [cuspAction, sl2zEntry]
  | coe r => simp [cuspAction, sl2zEntry]

/-- Auxiliary algebraic identity used in proving the multiplicative law for
`cuspAction`: handles the case where the denominator vanishes for `g₂`. -/
lemma cuspAction_factor_denom_zero (g₁ g₂ : SL(2, ℤ)) (r : ℚ)
    (hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0) :
    sl2zEntry (g₁ * g₂) 1 0 * r + sl2zEntry (g₁ * g₂) 1 1 =
    sl2zEntry g₁ 1 0 * (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) := by
  rw [sl2zEntry_mul, sl2zEntry_mul]
  have : sl2zEntry g₁ 1 1 * (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) = 0 := by
    rw [hd₂, mul_zero]
  linarith

/-- Companion identity to `cuspAction_factor_denom_zero` for the numerator. -/
lemma cuspAction_factor_numer_zero (g₁ g₂ : SL(2, ℤ)) (r : ℚ)
    (hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0) :
    sl2zEntry (g₁ * g₂) 0 0 * r + sl2zEntry (g₁ * g₂) 0 1 =
    sl2zEntry g₁ 0 0 * (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) := by
  rw [sl2zEntry_mul, sl2zEntry_mul]
  have : sl2zEntry g₁ 0 1 * (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) = 0 := by
    rw [hd₂, mul_zero]
  linarith

/-- If the denominator of the linear-fractional action of `g₂` on `r` vanishes, then
the numerator cannot also vanish (consequence of `det g₂ = 1`). -/
lemma cuspAction_numer_ne_zero_of_denom_zero (g₂ : SL(2, ℤ)) (r : ℚ)
    (hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0) :
    sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1 ≠ 0 := by
  intro heq
  have hdet := sl2zEntry_det g₂
  have : sl2zEntry g₂ 0 0 * (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) -
    sl2zEntry g₂ 1 0 * (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) = 1 := by linarith
  rw [hd₂, heq, mul_zero, mul_zero, sub_zero] at this
  exact zero_ne_one this

set_option maxHeartbeats 400000 in
/-- The cusp action at `∞` is compatible with multiplication in `SL₂(ℤ)`:
`(g₁ g₂) · ∞ = g₁ · (g₂ · ∞)`. -/
theorem cuspAction_mul_top (g₁ g₂ : SL(2, ℤ)) :
    cuspAction (g₁ * g₂) ⊤ = cuspAction g₁ (cuspAction g₂ ⊤) := by
  simp only [cuspAction]
  by_cases hc₂ : sl2zEntry g₂ 1 0 = 0
  · simp only [hc₂, ite_true]
    rw [sl2zEntry_mul]
    simp only [hc₂, mul_zero, add_zero]
    have ha₂ : sl2zEntry g₂ 0 0 ≠ 0 := by
      intro heq
      have := sl2zEntry_det g₂
      rw [hc₂, mul_zero, sub_zero, heq, zero_mul] at this
      exact zero_ne_one this
    by_cases hc₁ : sl2zEntry g₁ 1 0 = 0
    · simp [hc₁]
    · simp only [mul_ne_zero hc₁ ha₂, ite_false, hc₁]
      rw [sl2zEntry_mul]
      simp only [hc₂, mul_zero, add_zero]
      congr 1
      field_simp
  · simp only [hc₂, ite_false]
    rw [sl2zEntry_mul, sl2zEntry_mul]
    by_cases hdenom : sl2zEntry g₁ 1 0 * (sl2zEntry g₂ 0 0 / sl2zEntry g₂ 1 0) +
        sl2zEntry g₁ 1 1 = 0
    · have : sl2zEntry g₁ 1 0 * sl2zEntry g₂ 0 0 +
          sl2zEntry g₁ 1 1 * sl2zEntry g₂ 1 0 = 0 := by
        field_simp at hdenom
        linarith
      simp [this, hdenom]
    · have hne : sl2zEntry g₁ 1 0 * sl2zEntry g₂ 0 0 +
          sl2zEntry g₁ 1 1 * sl2zEntry g₂ 1 0 ≠ 0 := by
        intro heq
        apply hdenom
        field_simp
        linarith
      simp only [hne, hdenom, ite_false]
      congr 1
      field_simp

set_option maxHeartbeats 800000 in
/-- The cusp action at a rational cusp `r` is compatible with multiplication in
`SL₂(ℤ)`: `(g₁ g₂) · r = g₁ · (g₂ · r)`. -/
theorem cuspAction_mul_coe (g₁ g₂ : SL(2, ℤ)) (r : ℚ) :
    cuspAction (g₁ * g₂) ↑r = cuspAction g₁ (cuspAction g₂ ↑r) := by
  simp only [cuspAction]
  by_cases hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0
  · simp only [hd₂, ite_true]
    have hc₂_ne : sl2zEntry g₂ 1 0 ≠ 0 := by
      intro heq
      rw [heq, zero_mul, zero_add] at hd₂
      have := sl2zEntry_det g₂
      rw [hd₂, heq] at this
      simp at this
    have hnum₂_ne := cuspAction_numer_ne_zero_of_denom_zero g₂ r hd₂
    rw [cuspAction_factor_denom_zero g₁ g₂ r hd₂,
        cuspAction_factor_numer_zero g₁ g₂ r hd₂]
    by_cases hc₁ : sl2zEntry g₁ 1 0 = 0
    · simp [hc₁]
    · simp only [mul_ne_zero hc₁ hnum₂_ne, ite_false, hc₁]
      congr 1
      field_simp
  · simp only [hd₂, ite_false]
    set s := (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) /
             (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) with hs_def
    have hdenom_rel : sl2zEntry g₁ 1 0 * s + sl2zEntry g₁ 1 1 =
        (sl2zEntry (g₁ * g₂) 1 0 * r + sl2zEntry (g₁ * g₂) 1 1) /
        (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) := by
      rw [hs_def, sl2zEntry_mul, sl2zEntry_mul]
      have hd₂' : r * sl2zEntry g₂ 1 0 + sl2zEntry g₂ 1 1 ≠ 0 := by
        rwa [show r * sl2zEntry g₂ 1 0 + sl2zEntry g₂ 1 1 =
             sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 from by ring]
      field_simp
      ring
    have zero_iff : sl2zEntry g₁ 1 0 * s + sl2zEntry g₁ 1 1 = 0 ↔
        sl2zEntry (g₁ * g₂) 1 0 * r + sl2zEntry (g₁ * g₂) 1 1 = 0 := by
      rw [hdenom_rel, div_eq_zero_iff]
      exact ⟨fun h => h.resolve_right hd₂, fun h => Or.inl h⟩
    by_cases hprod : sl2zEntry (g₁ * g₂) 1 0 * r + sl2zEntry (g₁ * g₂) 1 1 = 0
    · have : sl2zEntry g₁ 1 0 * s + sl2zEntry g₁ 1 1 = 0 := zero_iff.mpr hprod
      simp [hprod, this]
    · have hne : sl2zEntry g₁ 1 0 * s + sl2zEntry g₁ 1 1 ≠ 0 :=
        fun h => hprod (zero_iff.mp h)
      simp only [hprod, hne, ite_false]
      congr 1
      rw [hs_def, sl2zEntry_mul, sl2zEntry_mul, sl2zEntry_mul, sl2zEntry_mul]
      have hd₂' : r * sl2zEntry g₂ 1 0 + sl2zEntry g₂ 1 1 ≠ 0 := by
        rwa [show r * sl2zEntry g₂ 1 0 + sl2zEntry g₂ 1 1 =
             sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 from by ring]
      field_simp
      ring

/-- Multiplicativity of the cusp action on all of `WithTop ℚ`, combining the cases
for the cusp at infinity and the finite rational cusps. -/
theorem cuspAction_mul (g₁ g₂ : SL(2, ℤ)) :
    ∀ x, cuspAction (g₁ * g₂) x = cuspAction g₁ (cuspAction g₂ x) := by
  intro x
  cases x with
  | top => exact cuspAction_mul_top g₁ g₂
  | coe r => exact cuspAction_mul_coe g₁ g₂ r

end ExtendedUpperHalfPlane
end ModularCurveX0Defs
end
