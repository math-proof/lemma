/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingGeneralSymbol.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.LogNonnegativeSinusoid
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Mathlib.Analysis.SpecialFunctions.Artanh
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingGeneralSymbol
open MeasureTheory


namespace StatMech.FrontierA

theorem triangularIsingSymbol_eq_innerSinusoid
    (J1 J2 J3 k1 k2 : Real) :
    triangularIsingSymbol J1 J2 J3 k1 k2 =
      triangularIsingInnerA J1 J2 J3 k1 -
        triangularIsingInnerU J2 J3 k1 * Real.cos k2 -
        triangularIsingInnerV J3 k1 * Real.sin k2 := by
  unfold triangularIsingSymbol triangularIsingInnerA
    triangularIsingInnerU triangularIsingInnerV
  rw [Real.cos_add]
  ring

theorem exp_neg_two_mul (J : Real) :
    Real.exp (-(2 * J)) = (Real.exp (2 * J))⁻¹ := by
  rw [← Real.exp_neg]

theorem triangularIsingInnerA_exp_identity
    (J1 J2 J3 k1 : Real) :
    let a := Real.exp (2 * J1)
    let b := Real.exp (2 * J2)
    let c := Real.exp (2 * J3)
    4 * a * b * c * triangularIsingInnerA J1 J2 J3 k1 =
      a ^ 2 * b ^ 2 * c ^ 2 + a ^ 2 + b ^ 2 + c ^ 2 +
        2 * b * c * (1 - a ^ 2) * Real.cos k1 := by
  dsimp only
  unfold triangularIsingInnerA
  rw [Real.cosh_eq, Real.cosh_eq, Real.cosh_eq,
    Real.sinh_eq, Real.sinh_eq, Real.sinh_eq,
    exp_neg_two_mul, exp_neg_two_mul, exp_neg_two_mul]
  field_simp [Real.exp_ne_zero]
  ring

theorem triangularIsingInnerA_pos
    (J1 J2 J3 k1 : Real) :
    0 < triangularIsingInnerA J1 J2 J3 k1 := by
  let a := Real.exp (2 * J1)
  let b := Real.exp (2 * J2)
  let c := Real.exp (2 * J3)
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  have hc : 0 < c := Real.exp_pos _
  have hxlo : -1 ≤ Real.cos k1 := Real.neg_one_le_cos k1
  have hxhi : Real.cos k1 ≤ 1 := Real.cos_le_one k1
  have hid := triangularIsingInnerA_exp_identity J1 J2 J3 k1
  dsimp only [a, b, c] at hid ⊢
  by_cases ha1 : 1 ≤ Real.exp (2 * J1)
  · have hcoeff : 2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
        (1 - Real.exp (2 * J1) ^ 2) ≤ 0 := by
      have : 1 ≤ Real.exp (2 * J1) ^ 2 := by nlinarith [Real.exp_pos (2 * J1)]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have hmul := mul_le_mul_of_nonpos_left hxhi hcoeff
    have hlowerEq :
        Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
            Real.exp (2 * J3) ^ 2 + Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 +
            2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
              (1 - Real.exp (2 * J1) ^ 2) =
          Real.exp (2 * J1) ^ 2 *
              (Real.exp (2 * J2) * Real.exp (2 * J3) - 1) ^ 2 +
            (Real.exp (2 * J2) + Real.exp (2 * J3)) ^ 2 := by ring
    have hlowerPos : 0 <
        Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
            Real.exp (2 * J3) ^ 2 + Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 +
            2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
              (1 - Real.exp (2 * J1) ^ 2) := by
      rw [hlowerEq]
      positivity
    have hNpos : 0 <
        Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
              Real.exp (2 * J3) ^ 2 + Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 +
          2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
            (1 - Real.exp (2 * J1) ^ 2) * Real.cos k1 := by
      linarith
    have hfactor : 0 < 4 * Real.exp (2 * J1) * Real.exp (2 * J2) *
        Real.exp (2 * J3) := by positivity
    rw [← hid] at hNpos
    rcases mul_pos_iff.mp hNpos with h | h
    · exact h.2
    · exact (lt_asymm hfactor h.1).elim
  · have ha1' : Real.exp (2 * J1) < 1 := lt_of_not_ge ha1
    have hcoeff : 0 ≤ 2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
        (1 - Real.exp (2 * J1) ^ 2) := by
      have : Real.exp (2 * J1) ^ 2 < 1 := by nlinarith [Real.exp_pos (2 * J1)]
      positivity
    have hmul := mul_le_mul_of_nonneg_left hxlo hcoeff
    have hlowerEq :
        Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
            Real.exp (2 * J3) ^ 2 + Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 -
            2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
              (1 - Real.exp (2 * J1) ^ 2) =
        Real.exp (2 * J1) ^ 2 *
            (Real.exp (2 * J2) * Real.exp (2 * J3) + 1) ^ 2 +
          (Real.exp (2 * J2) - Real.exp (2 * J3)) ^ 2 := by ring
    have hlowerPos : 0 <
        Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
            Real.exp (2 * J3) ^ 2 + Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 -
            2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
              (1 - Real.exp (2 * J1) ^ 2) := by
      rw [hlowerEq]
      positivity
    have hNpos : 0 <
        Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
              Real.exp (2 * J3) ^ 2 + Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 +
          2 * Real.exp (2 * J2) * Real.exp (2 * J3) *
            (1 - Real.exp (2 * J1) ^ 2) * Real.cos k1 := by
      linarith
    rw [← hid] at hNpos
    have hfactor : 0 < 4 * Real.exp (2 * J1) * Real.exp (2 * J2) *
        Real.exp (2 * J3) := by positivity
    rcases mul_pos_iff.mp hNpos with h | h
    · exact h.2
    · exact (lt_asymm hfactor h.1).elim

theorem triangularIsingInner_discriminant_exp_identity
    (J1 J2 J3 k1 : Real) :
    let a := Real.exp (2 * J1)
    let b := Real.exp (2 * J2)
    let c := Real.exp (2 * J3)
    let alpha := b * c * (a - 1) ^ 2
    let gamma := b * c * (a + 1) ^ 2
    let B := -(a ^ 2 * b ^ 2 * c ^ 2) - a ^ 2 + b ^ 2 + c ^ 2
    16 * a ^ 2 * b ^ 2 * c ^ 2 *
        (triangularIsingInnerA J1 J2 J3 k1 ^ 2 -
          (triangularIsingInnerU J2 J3 k1 ^ 2 +
            triangularIsingInnerV J3 k1 ^ 2)) =
      (B + (alpha + gamma) * Real.cos k1) ^ 2 +
        (alpha - gamma) ^ 2 * (1 - Real.cos k1 ^ 2) := by
  dsimp only
  unfold triangularIsingInnerA triangularIsingInnerU triangularIsingInnerV
  rw [Real.cosh_eq, Real.cosh_eq, Real.cosh_eq,
    Real.sinh_eq, Real.sinh_eq, Real.sinh_eq,
    exp_neg_two_mul, exp_neg_two_mul, exp_neg_two_mul]
  have htrig := Real.sin_sq_add_cos_sq k1
  have hsin : Real.sin k1 ^ 2 = 1 - Real.cos k1 ^ 2 := by linarith
  field_simp [Real.exp_ne_zero]
  rw [hsin]
  ring

theorem triangularIsingInner_discriminant_nonneg
    (J1 J2 J3 k1 : Real) :
    0 ≤ triangularIsingInnerA J1 J2 J3 k1 ^ 2 -
      (triangularIsingInnerU J2 J3 k1 ^ 2 +
        triangularIsingInnerV J3 k1 ^ 2) := by
  let a := Real.exp (2 * J1)
  let b := Real.exp (2 * J2)
  let c := Real.exp (2 * J3)
  let alpha := b * c * (a - 1) ^ 2
  let gamma := b * c * (a + 1) ^ 2
  let B := -(a ^ 2 * b ^ 2 * c ^ 2) - a ^ 2 + b ^ 2 + c ^ 2
  have hid := triangularIsingInner_discriminant_exp_identity J1 J2 J3 k1
  dsimp only [a, b, c, alpha, gamma, B] at hid ⊢
  have hcos : 0 ≤ 1 - Real.cos k1 ^ 2 := by
    nlinarith [Real.neg_one_le_cos k1, Real.cos_le_one k1]
  have hrhs : 0 ≤
      (-(Real.exp (2 * J1) ^ 2 * Real.exp (2 * J2) ^ 2 *
              Real.exp (2 * J3) ^ 2) - Real.exp (2 * J1) ^ 2 +
            Real.exp (2 * J2) ^ 2 + Real.exp (2 * J3) ^ 2 +
          (Real.exp (2 * J2) * Real.exp (2 * J3) *
                (Real.exp (2 * J1) - 1) ^ 2 +
            Real.exp (2 * J2) * Real.exp (2 * J3) *
                (Real.exp (2 * J1) + 1) ^ 2) * Real.cos k1) ^ 2 +
        (Real.exp (2 * J2) * Real.exp (2 * J3) *
              (Real.exp (2 * J1) - 1) ^ 2 -
            Real.exp (2 * J2) * Real.exp (2 * J3) *
              (Real.exp (2 * J1) + 1) ^ 2) ^ 2 *
          (1 - Real.cos k1 ^ 2) := by positivity
  have hfactor : 0 < 16 * Real.exp (2 * J1) ^ 2 *
      Real.exp (2 * J2) ^ 2 * Real.exp (2 * J3) ^ 2 := by positivity
  nlinarith


theorem triangularIsingSymbol_nonneg
    (J1 J2 J3 k1 k2 : Real) :
    0 ≤ triangularIsingSymbol J1 J2 J3 k1 k2 := by
  rw [triangularIsingSymbol_eq_innerSinusoid]
  let A := triangularIsingInnerA J1 J2 J3 k1
  let u := triangularIsingInnerU J2 J3 k1
  let v := triangularIsingInnerV J3 k1
  have hA : 0 < A := triangularIsingInnerA_pos J1 J2 J3 k1
  have hdisc : 0 ≤ A ^ 2 - (u ^ 2 + v ^ 2) :=
    triangularIsingInner_discriminant_nonneg J1 J2 J3 k1
  have hlinear : u * Real.cos k2 + v * Real.sin k2 ≤
      Real.sqrt (u ^ 2 + v ^ 2) := by
    have hcs := Real.sin_sq_add_cos_sq k2
    have hcauchy := sq_nonneg
      (u * Real.sin k2 - v * Real.cos k2)
    have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ u ^ 2 + v ^ 2)
    have hsq : (u * Real.cos k2 + v * Real.sin k2) ^ 2 ≤
        u ^ 2 + v ^ 2 := by nlinarith
    by_cases hlin : u * Real.cos k2 + v * Real.sin k2 ≤ 0
    · exact hlin.trans (Real.sqrt_nonneg _)
    · have hlinpos : 0 < u * Real.cos k2 + v * Real.sin k2 :=
        lt_of_not_ge hlin
      nlinarith [Real.sqrt_nonneg (u ^ 2 + v ^ 2)]
  have hsqrtLe : Real.sqrt (u ^ 2 + v ^ 2) ≤ A := by
    have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ u ^ 2 + v ^ 2)
    nlinarith [Real.sqrt_nonneg (u ^ 2 + v ^ 2)]
  dsimp only [A, u, v] at hlinear hsqrtLe ⊢
  linarith


theorem integral_log_triangularIsingSymbol_inner
    (J1 J2 J3 k1 : Real) :
    (∫ k2 in (-Real.pi)..Real.pi,
      Real.log (triangularIsingSymbol J1 J2 J3 k1 k2)) =
      2 * Real.pi * Real.log
        (nonnegativeSinusoidQ
          (triangularIsingInnerA J1 J2 J3 k1)
          (triangularIsingInnerU J2 J3 k1)
          (triangularIsingInnerV J3 k1) / 2) := by
  simp_rw [triangularIsingSymbol_eq_innerSinusoid]
  exact integral_log_nonnegativeSinusoid
    (triangularIsingInnerA_pos J1 J2 J3 k1)
    (triangularIsingInner_discriminant_nonneg J1 J2 J3 k1)


theorem continuous_triangularIsingFreeEnergyValue :
    Continuous (fun J : Real × Real × Real =>
      triangularIsingFreeEnergyValue J.1 J.2.1 J.2.2) := by
  let inner : (Real × Real × Real) → Real → Real := fun J k1 =>
    2 * Real.pi * Real.log
      (nonnegativeSinusoidQ
        (triangularIsingInnerA J.1 J.2.1 J.2.2 k1)
        (triangularIsingInnerU J.2.1 J.2.2 k1)
        (triangularIsingInnerV J.2.2 k1) / 2)
  have hinner : Continuous inner.uncurry := by
    apply Continuous.const_mul
    apply Continuous.log
    · unfold nonnegativeSinusoidQ triangularIsingInnerA
        triangularIsingInnerU triangularIsingInnerV
      fun_prop
    · intro p
      have hA := triangularIsingInnerA_pos p.1.1 p.1.2.1 p.1.2.2 p.2
      have hdisc := triangularIsingInner_discriminant_nonneg
        p.1.1 p.1.2.1 p.1.2.2 p.2
      exact (div_pos (nonnegativeSinusoidQ_pos hA hdisc) (by norm_num)).ne'
  have hintegral : Continuous (fun J : Real × Real × Real =>
      ∫ k1 in (-Real.pi)..Real.pi, inner J k1) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hinner (-Real.pi) Real.pi
  have hscaled : Continuous (fun J : Real × Real × Real =>
      -Real.log 2 - (1 / (8 * Real.pi ^ 2)) *
        ∫ k1 in (-Real.pi)..Real.pi, inner J k1) :=
    continuous_const.sub (continuous_const.mul hintegral)
  apply hscaled.congr
  intro J
  unfold triangularIsingFreeEnergyValue
  simp_rw [integral_log_triangularIsingSymbol_inner]
  rfl

end StatMech.FrontierA
