/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.Asymptotics.CatalanAsymptoticExpansion
/-!
# Stirling-type asymptotic expansions of Catalan numbers

This file proves all-orders logarithmic asymptotic expansions of the Catalan
numbers by solving their first-difference equation with Bernoulli polynomials.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma catalanExp_bernoulliPolynomialEval_eq (n : ℕ) (x : ℝ) :
    catalanExpBernoulliPolynomialEval n x =
      Polynomial.aeval x (Polynomial.bernoulli n) := rfl

lemma catalanExp_hasseDeriv_bernoulli (n k : ℕ) :
    Polynomial.hasseDeriv k (Polynomial.bernoulli n) =
      (n.choose k : ℚ) • Polynomial.bernoulli (n - k) := by
  ext i
  rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_bernoulli,
    Polynomial.coeff_smul, Polynomial.coeff_bernoulli]
  by_cases hik : i + k ≤ n
  · rw [ite_eq_left hik, ite_eq_left (by omega : i ≤ n - k)]
    have hc : (i + k).choose k * n.choose (i + k) =
        n.choose k * (n - k).choose i := by
      have hc' := Nat.choose_mul (n := n) (k := i + k) (s := k) (by omega)
      rw [show i + k - k = i by omega] at hc'
      simpa only [mul_comm] using hc'
    rw [show n - (i + k) = n - k - i by omega]
    have hc' : ((i + k).choose k : ℚ) * n.choose (i + k) =
        n.choose k * (n - k).choose i := by exact_mod_cast hc
    linear_combination (bernoulli (n - k - i) : ℚ) * hc'
  · rw [ite_eq_right hik]
    by_cases hk : k ≤ n
    · rw [ite_eq_right (by omega : ¬i ≤ n - k)]
      simp
    · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hk)]

lemma catalanExp_bernoulli_eval_add (n : ℕ) (x y : ℚ) :
    (Polynomial.bernoulli n).eval (x + y) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℚ) * (Polynomial.bernoulli (n - k)).eval x * y ^ k := by
  have htaylor : Polynomial.taylor x (Polynomial.bernoulli n) =
      ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k
        ((n.choose k : ℚ) * (Polynomial.bernoulli (n - k)).eval x) := by
    ext k
    rw [Polynomial.taylor_coeff, catalanExp_hasseDeriv_bernoulli,
      Polynomial.eval_smul]
    by_cases hk : k ≤ n
    · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
      · simp
      · intro b hb hbk
        rw [Polynomial.coeff_monomial, ite_eq_right hbk]
      · simp [hk]
    · have hkn : n < k := by omega
      rw [Nat.choose_eq_zero_of_lt hkn, Nat.cast_zero, zero_smul,
        Polynomial.finsetSum_coeff]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      have hbn : b ≤ n := by simpa using (Finset.mem_range.mp hb)
      have hbk : b ≠ k := by omega
      rw [Polynomial.coeff_monomial, ite_eq_right hbk]
  calc
    (Polynomial.bernoulli n).eval (x + y) =
        (Polynomial.taylor x (Polynomial.bernoulli n)).eval y := by
      rw [Polynomial.taylor_eval, add_comm]
    _ = _ := by
      rw [htaylor, Polynomial.eval_finsetSum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Polynomial.eval_monomial]

lemma catalanExp_bernoulli_eval_add' (n : ℕ) (x y : ℚ) :
    (Polynomial.bernoulli n).eval (x + y) =
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x * y ^ (n - k) := by
  rw [catalanExp_bernoulli_eval_add, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using (Finset.mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega]
  rw [show n - (n - k) = k by omega, Nat.choose_symm hkn]

lemma catalanExp_pow_mul_inv_pow {a : ℚ} (ha : a ≠ 0) {k n : ℕ} (hkn : k ≤ n) :
    a ^ n * a⁻¹ ^ (n - k) = a ^ k := by
  rw [inv_pow, ← pow_sub_mul_pow a hkn]
  field_simp

lemma catalanExp_sum_range_even_odd {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 2), f k =
      ∑ r ∈ Finset.range (m + 1), (f (2 * r) + f (2 * r + 1)) := by
  induction m with
  | zero => simp [Finset.sum_range_succ]
  | succ m ih =>
      conv_lhs =>
        rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [ih]
      simp only [show 2 * m + 2 = 2 * (m + 1) by omega,
        show 2 * m + 2 + 1 = 2 * (m + 1) + 1 by omega, add_assoc]

lemma catalanExp_bernoulli_eval_half_odd (m : ℕ) :
    (Polynomial.bernoulli (2 * m + 1)).eval (1 / 2 : ℚ) = 0 := by
  have h := Polynomial.bernoulli_eval_one_sub (2 * m + 1) (1 / 2 : ℚ)
  norm_num [Even.neg_one_pow, Odd.neg_one_pow, show Odd (2 * m + 1) from ⟨m, by omega⟩] at h
  linarith

lemma catalanExp_bernoulli_eval_zero_odd (m : ℕ) (hm : 0 < m) :
    (Polynomial.bernoulli (2 * m + 1)).eval 0 = 0 := by
  rw [Polynomial.bernoulli_eval_zero,
    bernoulli_eq_zero_of_odd (⟨m, by omega⟩ : Odd (2 * m + 1)) (by omega)]

lemma catalanExp_weighted_bernoulli_add (n : ℕ) (x a : ℚ) (ha : a ≠ 0) :
    ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x * a ^ k =
      a ^ n * (Polynomial.bernoulli n).eval (x + a⁻¹) := by
  rw [catalanExp_bernoulli_eval_add', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using (Finset.mem_range.mp hk)
  calc
    (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x * a ^ k =
        (n.choose k : ℚ) * (Polynomial.bernoulli k).eval x *
          (a ^ n * a⁻¹ ^ (n - k)) := by
      rw [catalanExp_pow_mul_inv_pow ha hkn]
    _ = a ^ n * ((n.choose k : ℚ) * (Polynomial.bernoulli k).eval x *
          a⁻¹ ^ (n - k)) := by ring

lemma catalanExp_odd_weighted_bernoulli_sum (m : ℕ) (hm : 0 < m) :
    ∑ r ∈ Finset.range (m + 1),
        ((2 * m + 1).choose (2 * r + 1) : ℚ) *
          (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
            (4 : ℚ) ^ (2 * r + 1) = 0 := by
  have hplus : (∑ k ∈ Finset.range (2 * m + 2),
      ((2 * m + 1).choose k : ℚ) *
        (Polynomial.bernoulli k).eval (1 / 4) * (4 : ℚ) ^ k) = 0 := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
      catalanExp_weighted_bernoulli_add (2 * m + 1) (1 / 4) 4 (by norm_num)]
    norm_num [catalanExp_bernoulli_eval_half_odd]
  have hminus : (∑ k ∈ Finset.range (2 * m + 2),
      ((2 * m + 1).choose k : ℚ) *
        (Polynomial.bernoulli k).eval (1 / 4) * (-4 : ℚ) ^ k) = 0 := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega,
      catalanExp_weighted_bernoulli_add (2 * m + 1) (1 / 4) (-4) (by norm_num)]
    norm_num [catalanExp_bernoulli_eval_zero_odd m hm]
  let f : ℕ → ℚ := fun k => ((2 * m + 1).choose k : ℚ) *
    (Polynomial.bernoulli k).eval (1 / 4) * ((4 : ℚ) ^ k - (-4 : ℚ) ^ k)
  have hdiff : ∑ k ∈ Finset.range (2 * m + 2), f k = 0 := by
    calc
      ∑ k ∈ Finset.range (2 * m + 2), f k =
          (∑ k ∈ Finset.range (2 * m + 2),
            ((2 * m + 1).choose k : ℚ) *
              (Polynomial.bernoulli k).eval (1 / 4) * (4 : ℚ) ^ k) -
          ∑ k ∈ Finset.range (2 * m + 2),
            ((2 * m + 1).choose k : ℚ) *
              (Polynomial.bernoulli k).eval (1 / 4) * (-4 : ℚ) ^ k := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [f]
        ring
      _ = 0 := by rw [hplus, hminus, sub_zero]
  rw [catalanExp_sum_range_even_odd f m] at hdiff
  have hpair (r : ℕ) : f (2 * r) + f (2 * r + 1) =
      2 * (((2 * m + 1).choose (2 * r + 1) : ℚ) *
        (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
          (4 : ℚ) ^ (2 * r + 1)) := by
    have heven : Even (2 * r) := ⟨r, by omega⟩
    have hodd : Odd (2 * r + 1) := ⟨r, by omega⟩
    dsimp [f]
    rw [neg_pow, heven.neg_one_pow, neg_pow, hodd.neg_one_pow]
    ring
  simp_rw [hpair] at hdiff
  rw [← Finset.mul_sum] at hdiff
  linarith

end MetaMathlibExt
