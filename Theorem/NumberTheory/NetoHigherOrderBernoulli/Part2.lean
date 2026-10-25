/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NetoHigherOrderBernoulli.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Polynomial.Roots
import Def.NumberTheory.NetoHigherOrderBernoulli
/-! # Neto's symmetry identity for higher-order Bernoulli numbers

This file defines higher-order Bernoulli numbers through their formal exponential generating
series and proves Neto's symmetry identity for them.
-/


namespace MetaMathlibExt

open Finset

theorem neto_choose_eq_eval (x : ℂ) (j : ℕ) :
    Ring.choose x j = Polynomial.eval x (neto_choosePolynomial j) := by
  rw [Ring.choose_eq_smul]
  simp only [neto_choosePolynomial, smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_C]
  rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval,
    ← descPochhammer_eval_eq_ascPochhammer]

theorem neto_coeff_pow_bernoulli_sub_one_eq_zero {m j : ℕ} (h : m < j) :
    PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero j ?_)
  · exact_mod_cast h
  · simp [bernoulliPowerSeries]

theorem neto_coeff_subst_binomial (x : ℂ) (m : ℕ) :
    PowerSeries.coeff m
        (PowerSeries.subst (bernoulliPowerSeries ℂ - 1)
          (PowerSeries.binomialSeries ℂ x)) =
      ∑ j ∈ Finset.range (m + 1), Ring.choose x j *
        PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j) := by
  rw [PowerSeries.coeff_subst' neto_hasSubst_bernoulli_sub_one]
  have hs : Function.support (fun j : ℕ =>
      PowerSeries.coeff j (PowerSeries.binomialSeries ℂ x) •
        PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j)) ⊆
      (Finset.range (m + 1) : Set ℕ) := by
    intro j hj
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    apply hj
    have hmj : m < j := by omega
    change PowerSeries.coeff j (PowerSeries.binomialSeries ℂ x) •
      PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j) = 0
    rw [neto_coeff_pow_bernoulli_sub_one_eq_zero hmj, smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]

end MetaMathlibExt
