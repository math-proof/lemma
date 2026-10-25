/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.KummerExtension
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicProduct.Part2
open scoped BigOperators


namespace StatMech.FrontierA

theorem quantumIsingAntiperiodicRoot_eq_exp
    (n j : Nat) (hn : n ≠ 0) :
    quantumIsingAntiperiodicRoot n j =
      Complex.exp ((quantumIsingAntiperiodicAngle n j : Real) * Complex.I) := by
  unfold quantumIsingAntiperiodicRoot quantumIsingAntiperiodicAngle
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have hnC : (n : Complex) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp [hnC]
  push_cast
  field_simp [hnC]

theorem quantumIsingAntiperiodicRoot_re
    (n j : Nat) (hn : n ≠ 0) :
    (quantumIsingAntiperiodicRoot n j).re =
      Real.cos (quantumIsingAntiperiodicAngle n j) := by
  rw [quantumIsingAntiperiodicRoot_eq_exp n j hn, Complex.exp_mul_I]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem quantumIsingAntiperiodicRoot_im
    (n j : Nat) (hn : n ≠ 0) :
    (quantumIsingAntiperiodicRoot n j).im =
      Real.sin (quantumIsingAntiperiodicAngle n j) := by
  rw [quantumIsingAntiperiodicRoot_eq_exp n j hn, Complex.exp_mul_I]
  simp [Complex.sin_ofReal_re]

theorem normSq_one_sub_real_mul_antiperiodicRoot
    (n j : Nat) (hn : n ≠ 0) (z : Real) :
    Complex.normSq (1 - (z : Complex) * quantumIsingAntiperiodicRoot n j) =
      1 - 2 * z * Real.cos (quantumIsingAntiperiodicAngle n j) + z ^ 2 := by
  rw [Complex.normSq_apply]
  simp [quantumIsingAntiperiodicRoot_re n j hn,
    quantumIsingAntiperiodicRoot_im n j hn]
  nlinarith [Real.sin_sq_add_cos_sq (quantumIsingAntiperiodicAngle n j)]


theorem prod_sub_cos_quantumIsingAntiperiodicAngle
    (n : Nat) (hn : n ≠ 0) (r : Real) (hr : 0 < r) :
    (∏ j ∈ Finset.range n,
      ((r + r⁻¹) / 2 - Real.cos (quantumIsingAntiperiodicAngle n j))) =
      (r / 2) ^ n * (1 + r⁻¹ ^ n) ^ 2 := by
  let z : Real := r⁻¹
  have hr0 : r ≠ 0 := hr.ne'
  have hfactor (j : Nat) :
      (r + r⁻¹) / 2 - Real.cos (quantumIsingAntiperiodicAngle n j) =
        (r / 2) * (1 - 2 * z * Real.cos (quantumIsingAntiperiodicAngle n j) + z ^ 2) := by
    dsimp [z]
    field_simp [hr0]
    ring
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hnorm :
      (∏ j ∈ Finset.range n,
        (1 - 2 * z * Real.cos (quantumIsingAntiperiodicAngle n j) + z ^ 2)) =
      Complex.normSq (∏ j ∈ Finset.range n,
        (1 - (z : Complex) * quantumIsingAntiperiodicRoot n j)) := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j hj
    exact (normSq_one_sub_real_mul_antiperiodicRoot n j hn z).symm
  rw [hnorm, prod_one_sub_quantumIsingAntiperiodicRoot n hn (z : Complex)]
  congr 1
  change Complex.normSq (1 + ((r⁻¹ : Real) : Complex) ^ n) =
    (1 + r⁻¹ ^ n) ^ 2
  have hzpow : (((r⁻¹ : Real) : Complex) ^ n) =
      (((r⁻¹ : Real) ^ n : Real) : Complex) := by
    exact_mod_cast rfl
  rw [hzpow, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re,
    Complex.add_im, Complex.one_im, Complex.ofReal_im, add_zero,
    zero_mul]
  ring

end StatMech.FrontierA

namespace StatMech.FrontierA


theorem sum_log_sub_cos_quantumIsingAntiperiodicAngle
    (n : Nat) (hn : n ≠ 0) (r : Real) (hr : 1 < r) :
    (∑ j ∈ Finset.range n,
      Real.log ((r + r⁻¹) / 2 -
        Real.cos (quantumIsingAntiperiodicAngle n j))) =
      -(n : Real) * Real.log 2 + (n : Real) * Real.log r +
        2 * Real.log (1 + r⁻¹ ^ n) := by
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hr0 : r ≠ 0 := hrpos.ne'
  have ha : 1 < (r + r⁻¹) / 2 := by
    have hsquare : 0 < (r - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hr)
    have hdiv : 0 < (r - 1) ^ 2 / r := div_pos hsquare hrpos
    field_simp [hr0] at hdiv ⊢
    nlinarith
  have hfactor (j : Nat) : 0 <
      (r + r⁻¹) / 2 - Real.cos (quantumIsingAntiperiodicAngle n j) :=
    sub_pos.mpr ((Real.cos_le_one _).trans_lt ha)
  rw [← Real.log_prod (fun j hj => (hfactor j).ne')]
  rw [prod_sub_cos_quantumIsingAntiperiodicAngle n hn r hrpos]
  have hrhalf : r / 2 ≠ 0 := div_ne_zero hr0 (by norm_num)
  have hone : 1 + r⁻¹ ^ n ≠ 0 := by positivity
  rw [Real.log_mul (pow_ne_zero _ hrhalf) (pow_ne_zero _ hone),
    Real.log_pow, Real.log_pow, Real.log_div hr0 (by norm_num)]
  ring

end StatMech.FrontierA
