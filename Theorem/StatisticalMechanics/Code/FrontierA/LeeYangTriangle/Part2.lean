/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangTriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Def.StatisticalMechanics.Code.FrontierA.LeeYangTriangle.Part2
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB


theorem minusSpinCount_finThree (s : ConfigSpace (Fin 3)) :
    minusSpinCount s =
      (if s 0 = false then 1 else 0) +
      (if s 1 = false then 1 else 0) +
      (if s 2 = false then 1 else 0) := by
  calc
    minusSpinCount s = ∑ x : Fin 3, if s x = false then 1 else 0 := by
      simp [minusSpinCount]
    _ = _ := by rw [Fin.sum_univ_three]

set_option maxHeartbeats 800000 in


theorem leeYangPolynomial_threeVertexTriangle (beta : ℝ) :
    leeYangPolynomial threeVertexTriangle beta =
      C (Real.exp (3 * beta)) * (1 + X ^ 3) +
        C (3 * Real.exp (-beta)) * (X + X ^ 2) := by
  unfold leeYangPolynomial zeroFieldInteractionWeight
  rw [← Equiv.sum_comp piFinThreeBoolEquiv.symm]
  simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp_rw [sum_bond_threeVertexTriangle]
  simp_rw [minusSpinCount_finThree]
  simp only [piFinThreeBoolEquiv, Equiv.coe_fn_symm_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Fin.isValue, bond_mk, spin, mul_one, mul_neg, Bool.true_eq_false,
    Bool.false_eq_true, ↓reduceIte, add_zero, zero_add, pow_zero, pow_one,
    Nat.reduceAdd, map_mul]
  rw [Polynomial.C_ofNat]
  ring_nf


theorem leeYangPolynomial_threeVertexTriangle_factored (beta : ℝ) :
    leeYangPolynomial threeVertexTriangle beta =
      C (Real.exp (3 * beta)) *
        (X + 1) *
          (X ^ 2 + C (3 * Real.exp (-4 * beta) - 1) * X + 1) := by
  rw [leeYangPolynomial_threeVertexTriangle]
  have hexp : Real.exp (3 * beta) * (3 * Real.exp (-4 * beta)) =
      3 * Real.exp (-beta) := by
    calc
      Real.exp (3 * beta) * (3 * Real.exp (-4 * beta)) =
          3 * (Real.exp (3 * beta) * Real.exp (-4 * beta)) := by ring
      _ = 3 * Real.exp (3 * beta + -4 * beta) := by rw [Real.exp_add]
      _ = 3 * Real.exp (-beta) := by ring_nf
  rw [show C (3 * Real.exp (-beta)) =
      C (Real.exp (3 * beta)) * C (3 * Real.exp (-4 * beta)) by
        rw [← map_mul, hexp]]
  simp only [map_sub, map_one]
  ring


theorem leeYangComplexPolynomial_threeVertexTriangle_factored (beta : ℝ) :
    leeYangComplexPolynomial threeVertexTriangle beta =
      C (Real.exp (3 * beta) : ℂ) *
        (X + 1) *
          (X ^ 2 + C (3 * Real.exp (-4 * beta) - 1 : ℂ) * X + 1) := by
  unfold leeYangComplexPolynomial
  rw [leeYangPolynomial_threeVertexTriangle_factored]
  simp


theorem palindromicQuadratic_root_norm {c : ℝ} (hcLower : -2 ≤ c)
    (hcUpper : c ≤ 2) {z : ℂ} (hz : z ^ 2 + (c : ℂ) * z + 1 = 0) :
    ‖z‖ = 1 := by
  have hre : z.re ^ 2 - z.im ^ 2 + c * z.re + 1 = 0 := by
    have h := congrArg Complex.re hz
    simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re] at h
    norm_num at h
    nlinarith
  have him : z.im * (2 * z.re + c) = 0 := by
    have h := congrArg Complex.im hz
    simp only [pow_two, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_im] at h
    norm_num at h
    nlinarith
  have hcSq : c ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg (c + 2), sq_nonneg (2 - c)]
  have hnormSq : Complex.normSq z = 1 := by
    rw [Complex.normSq_apply]
    rcases mul_eq_zero.mp him with himZero | hlinear
    · have hdisc : (2 * z.re + c) ^ 2 = c ^ 2 - 4 := by
        nlinarith [hre]
      have hdiscNonneg : 0 ≤ c ^ 2 - 4 := by
        nlinarith [sq_nonneg (2 * z.re + c)]
      have hlin : 2 * z.re + c = 0 := by
        nlinarith [sq_nonneg (2 * z.re + c)]
      nlinarith
    · nlinarith
  rw [Complex.normSq_eq_norm_sq] at hnormSq
  nlinarith [norm_nonneg z]


theorem leeYang_threeVertexTriangle_root_norm {beta : ℝ} (hbeta : 0 ≤ beta)
    {z : ℂ} (hz : (leeYangComplexPolynomial threeVertexTriangle beta).eval z = 0) :
    ‖z‖ = 1 := by
  rw [leeYangComplexPolynomial_threeVertexTriangle_factored] at hz
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at hz
  rcases mul_eq_zero.mp hz with hleft | hquad
  · rcases mul_eq_zero.mp hleft with hexp | hlinear
    · have hExp : (Real.exp (3 * beta) : ℂ) ≠ 0 := by
        exact_mod_cast Real.exp_ne_zero (3 * beta)
      exact False.elim (hExp hexp)
    · have : z = -1 := by
        exact add_eq_zero_iff_eq_neg.mp hlinear
      simp [this]
  · let c : ℝ := 3 * Real.exp (-4 * beta) - 1
    have hExpLe : Real.exp (-4 * beta) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      linarith
    have hcLower : -2 ≤ c := by
      dsimp [c]
      nlinarith [Real.exp_pos (-4 * beta)]
    have hcUpper : c ≤ 2 := by
      dsimp [c]
      nlinarith [hExpLe]
    apply palindromicQuadratic_root_norm hcLower hcUpper
    simpa only [c, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_exp, Complex.ofReal_one] using hquad


theorem hasLeeYangCircle_threeVertexTriangle {beta : ℝ} (hbeta : 0 ≤ beta) :
    HasLeeYangCircle threeVertexTriangle beta := by
  intro z hz
  exact leeYang_threeVertexTriangle_root_norm hbeta hz


end StatMech.FrontierA
