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
import Def.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part2
/-!
# Stirling-type asymptotic expansions of Catalan numbers

This file proves all-orders logarithmic asymptotic expansions of the Catalan
numbers by solving their first-difference equation with Bernoulli polynomials.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma catalanExpEulerEvenQ_zero : catalanExpEulerEvenQ 0 = 1 := by
  norm_num [catalanExpEulerEvenQ, Polynomial.bernoulli_one]

lemma catalanExpEulerEvenQ_recurrence (m : ℕ) :
    ∑ r ∈ Finset.range (m + 1),
        ((2 * m).choose (2 * r) : ℚ) * catalanExpEulerEvenQ r =
      if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [catalanExpEulerEvenQ_zero]
  · rw [ite_eq_right hm]
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hterm (r : ℕ) : ((2 * m).choose (2 * r) : ℚ) * catalanExpEulerEvenQ r =
        -(1 / (2 * m + 1 : ℚ)) *
          (((2 * m + 1).choose (2 * r + 1) : ℚ) *
            (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
              (4 : ℚ) ^ (2 * r + 1)) := by
      have hc := Nat.add_one_mul_choose_eq (2 * m) (2 * r)
      have hc' : (2 * m + 1 : ℚ) * (2 * m).choose (2 * r) =
          ((2 * m + 1).choose (2 * r + 1) : ℚ) * (2 * r + 1) := by
        exact_mod_cast hc
      have hratio : ((2 * m).choose (2 * r) : ℚ) / (2 * r + 1 : ℕ) =
          ((2 * m + 1).choose (2 * r + 1) : ℚ) / (2 * m + 1 : ℕ) := by
        apply (div_eq_div_iff (by positivity) (by positivity)).2
        push_cast at hc' ⊢
        nlinarith [hc']
      dsimp [catalanExpEulerEvenQ]
      calc
        ((2 * m).choose (2 * r) : ℚ) *
            (-(4 : ℚ) ^ (2 * r + 1) *
              (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) /
                (2 * r + 1 : ℕ)) =
            -(((2 * m).choose (2 * r) : ℚ) / (2 * r + 1 : ℕ)) *
              ((Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
                (4 : ℚ) ^ (2 * r + 1)) := by ring
        _ = -(((2 * m + 1).choose (2 * r + 1) : ℚ) / (2 * m + 1 : ℕ)) *
              ((Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
                (4 : ℚ) ^ (2 * r + 1)) := by rw [hratio]
        _ = _ := by
          push_cast
          ring
    calc
      ∑ r ∈ Finset.range (m + 1),
          ((2 * m).choose (2 * r) : ℚ) * catalanExpEulerEvenQ r =
          -(1 / (2 * m + 1 : ℚ)) *
            ∑ r ∈ Finset.range (m + 1),
              (((2 * m + 1).choose (2 * r + 1) : ℚ) *
                (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4) *
                  (4 : ℚ) ^ (2 * r + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        exact hterm r
      _ = 0 := by rw [catalanExp_odd_weighted_bernoulli_sum m hmpos, mul_zero]

lemma catalanExp_even_binom_sum_reflect (m : ℕ) (f : ℕ → ℚ) :
    ∑ j ∈ Finset.range (m + 1), ((2 * m).choose (2 * j) : ℚ) * f (m - j) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m).choose (2 * j) : ℚ) * f j := by
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by simpa using (Finset.mem_range.mp hj)
  rw [show m + 1 - 1 - j = m - j by omega,
    show 2 * (m - j) = 2 * m - 2 * j by omega,
    Nat.choose_symm (by omega : 2 * j ≤ 2 * m),
    show m - (m - j) = j by omega]

lemma catalanExp_even_E_eq (E : ℕ → ℤ)
    (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0) (m : ℕ) :
    (E (2 * m) : ℚ) = catalanExpEulerEvenQ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm : m = 0
      · subst m
        rw [mul_zero, hE.1, Int.cast_one, catalanExpEulerEvenQ_zero]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hEraw := hE.2 (2 * m) (by omega)
        have hErawQ : (∑ j ∈ Finset.range (m + 1),
            ((2 * m).choose (2 * j) : ℚ) * (E (2 * m - 2 * j) : ℚ)) = 0 := by
          have hcast := congrArg (fun z : ℤ => (z : ℚ)) hEraw
          push_cast at hcast
          simpa only [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] using hcast
        have hEoriented : (∑ r ∈ Finset.range (m + 1),
            ((2 * m).choose (2 * r) : ℚ) * (E (2 * r) : ℚ)) = 0 := by
          rw [← catalanExp_even_binom_sum_reflect m (fun r => (E (2 * r) : ℚ))]
          convert hErawQ using 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [show 2 * m - 2 * j = 2 * (m - j) by omega]
        have hQ := catalanExpEulerEvenQ_recurrence m
        rw [ite_eq_right hm] at hQ
        rw [Finset.sum_range_succ] at hEoriented hQ
        have hprefix : (∑ r ∈ Finset.range m,
            ((2 * m).choose (2 * r) : ℚ) * (E (2 * r) : ℚ)) =
            ∑ r ∈ Finset.range m,
              ((2 * m).choose (2 * r) : ℚ) * catalanExpEulerEvenQ r := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [ih r (Finset.mem_range.mp hr)]
        rw [hprefix] at hEoriented
        simp only [Nat.choose_self, Nat.cast_one, one_mul] at hEoriented hQ
        linarith

lemma catalanExp_bernoulli_quarter_eq (E : ℕ → ℤ)
    (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0) (m : ℕ) :
    (Polynomial.bernoulli (2 * m + 1)).eval (1 / 4) =
      -(2 * m + 1 : ℚ) * (E (2 * m) : ℚ) / (4 : ℚ) ^ (2 * m + 1) := by
  have h := catalanExp_even_E_eq E hE m
  rw [catalanExpEulerEvenQ] at h
  have hn : (2 * m + 1 : ℚ) ≠ 0 := by positivity
  have hp : (4 : ℚ) ^ (2 * m + 1) ≠ 0 := by positivity
  field_simp [hn, hp] at h ⊢
  push_cast at h ⊢
  linear_combination h

lemma catalanExp_bernoulliPolynomialEval_eq_fun (n : ℕ) (x : ℝ) :
    catalanExpBernoulliPolynomialEval n x = bernoulliFun n x := by
  rw [catalanExp_bernoulliPolynomialEval_eq]
  simp only [bernoulliFun, Polynomial.aeval_def, Polynomial.eval_map]

lemma catalanExp_bernoulliPolynomialEval_rat (n : ℕ) (x : ℚ) :
    catalanExpBernoulliPolynomialEval n (x : ℝ) =
      algebraMap ℚ ℝ ((Polynomial.bernoulli n).eval x) := by
  rw [catalanExp_bernoulliPolynomialEval_eq_fun]
  change (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli n)).eval
      (algebraMap ℚ ℝ x) =
    algebraMap ℚ ℝ ((Polynomial.bernoulli n).eval x)
  exact Polynomial.eval_map_apply (f := algebraMap ℚ ℝ)
    (p := Polynomial.bernoulli n) x

lemma catalanExp_bernoulliPolynomialEval_two (n : ℕ) (hn : n ≠ 1) :
    catalanExpBernoulliPolynomialEval n 2 = (bernoulli n : ℝ) + n := by
  rw [show (2 : ℝ) = ((2 : ℚ) : ℝ) by norm_num,
    catalanExp_bernoulliPolynomialEval_rat]
  have hQ : (Polynomial.bernoulli n).eval (2 : ℚ) = bernoulli n + n := by
    calc
      (Polynomial.bernoulli n).eval (2 : ℚ) =
          (Polynomial.bernoulli n).eval (1 + 1) := by norm_num
      _ = (Polynomial.bernoulli n).eval 1 + n * (1 : ℚ) ^ (n - 1) :=
        Polynomial.bernoulli_eval_one_add n 1
      _ = bernoulli n + n := by
        rw [Polynomial.bernoulli_eval_one, bernoulli_eq_bernoulli'_of_ne_one hn]
        norm_num
  simpa only [map_add, map_natCast, eq_ratCast] using congrArg (algebraMap ℚ ℝ) hQ

lemma catalanExp_first_bernoulli_difference (j : ℕ) :
    catalanExpBernoulliPolynomialEval (j + 2) (1 / 2) -
        catalanExpBernoulliPolynomialEval (j + 2) 2 =
      (((2 : ℝ) ^ (j + 1))⁻¹ - 2) * (bernoulli (j + 2) : ℝ) -
        (j + 1 : ℕ) - 1 := by
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    catalanExp_bernoulliPolynomialEval_eq_fun,
    bernoulliFun_eval_half, catalanExp_bernoulliPolynomialEval_two (j + 2) (by omega)]
  have hpow : (2 : ℝ) / 2 ^ (j + 2) = ((2 : ℝ) ^ (j + 1))⁻¹ := by
    rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
    field_simp
  rw [hpow]
  push_cast
  ring

lemma catalanExp_second_odd_bernoulli_difference (r : ℕ) :
    catalanExpBernoulliPolynomialEval (2 * r + 2) (-1 / 4) -
        catalanExpBernoulliPolynomialEval (2 * r + 2) (5 / 4) = 0 := by
  have hQ : (Polynomial.bernoulli (2 * r + 2)).eval (-1 / 4) -
      (Polynomial.bernoulli (2 * r + 2)).eval (5 / 4) = 0 := by
    have h := Polynomial.bernoulli_eval_one_sub (2 * r + 2) (-1 / 4 : ℚ)
    have heven : Even (2 * r + 2) := ⟨r + 1, by omega⟩
    rw [heven.neg_one_pow] at h
    norm_num at h
    linarith
  rw [show (-1 / 4 : ℝ) = ((-1 / 4 : ℚ) : ℝ) by norm_num,
    show (5 / 4 : ℝ) = ((5 / 4 : ℚ) : ℝ) by norm_num,
    catalanExp_bernoulliPolynomialEval_rat,
    catalanExp_bernoulliPolynomialEval_rat]
  simpa only [map_sub, map_zero] using congrArg (algebraMap ℚ ℝ) hQ

lemma catalanExp_second_even_coefficient (E : ℕ → ℤ)
    (hE : E 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      (∑ j ∈ Finset.range (n / 2 + 1),
        (n.choose (2 * j) : ℤ) * E (n - 2 * j)) = 0)
    (r : ℕ) (hr : 0 < r) :
    (-1 : ℝ) ^ (2 * r + 1) *
        (catalanExpBernoulliPolynomialEval (2 * r + 1) (-1 / 4) -
          catalanExpBernoulliPolynomialEval (2 * r + 1) (5 / 4)) /
          ((2 * r : ℕ) * (2 * r + 1 : ℕ)) =
      ((2 : ℝ) ^ (4 * r + 2))⁻¹ * (4 - (E (2 * r) : ℝ)) / r := by
  let B : ℚ := (Polynomial.bernoulli (2 * r + 1)).eval (1 / 4)
  have hneg : (Polynomial.bernoulli (2 * r + 1)).eval (-1 / 4) =
      -(B + (2 * r + 1 : ℚ) * (1 / 4) ^ (2 * r)) := by
    have h := Polynomial.bernoulli_eval_neg (2 * r + 1) (1 / 4 : ℚ)
    have hodd : Odd (2 * r + 1) := ⟨r, by omega⟩
    rw [hodd.neg_one_pow, show 2 * r + 1 - 1 = 2 * r by omega] at h
    push_cast at h ⊢
    norm_num at h ⊢
    simpa only [B, neg_mul, one_mul] using h
  have hplus : (Polynomial.bernoulli (2 * r + 1)).eval (5 / 4) =
      B + (2 * r + 1 : ℚ) * (1 / 4) ^ (2 * r) := by
    have h := Polynomial.bernoulli_eval_one_add (2 * r + 1) (1 / 4 : ℚ)
    norm_num at h ⊢
    simpa only [B, show 2 * r + 1 - 1 = 2 * r by omega] using h
  have hB := catalanExp_bernoulli_quarter_eq E hE r
  change B = -(2 * r + 1 : ℚ) * (E (2 * r) : ℚ) /
    (4 : ℚ) ^ (2 * r + 1) at hB
  have htwo : (2 : ℚ) ^ (4 * r + 2) = (4 : ℚ) ^ (2 * r + 1) := by
    calc
      (2 : ℚ) ^ (4 * r + 2) = 2 ^ (2 * (2 * r + 1)) := by
        congr 1
        omega
      _ = (2 ^ 2) ^ (2 * r + 1) := by rw [pow_mul]
      _ = (4 : ℚ) ^ (2 * r + 1) := by norm_num
  have hcoefQ : (-1 : ℚ) ^ (2 * r + 1) *
      ((Polynomial.bernoulli (2 * r + 1)).eval (-1 / 4) -
        (Polynomial.bernoulli (2 * r + 1)).eval (5 / 4)) /
        ((2 * r : ℕ) * (2 * r + 1 : ℕ)) =
      ((2 : ℚ) ^ (4 * r + 2))⁻¹ * (4 - (E (2 * r) : ℚ)) / r := by
    rw [hneg, hplus, hB, htwo]
    have hodd : Odd (2 * r + 1) := ⟨r, by omega⟩
    rw [hodd.neg_one_pow, show 2 * r + 1 = 2 * r + 1 by rfl, pow_succ,
      div_pow]
    norm_num
    field_simp
    ring
  rw [show (-1 / 4 : ℝ) = ((-1 / 4 : ℚ) : ℝ) by norm_num,
    show (5 / 4 : ℝ) = ((5 / 4 : ℚ) : ℝ) by norm_num,
    catalanExp_bernoulliPolynomialEval_rat,
    catalanExp_bernoulliPolynomialEval_rat]
  have hcast := congrArg (algebraMap ℚ ℝ) hcoefQ
  simp only [map_mul, map_sub, map_div₀, map_pow, map_inv₀, map_natCast,
    map_intCast, eq_ratCast] at hcast
  push_cast at hcast ⊢
  simpa only [eq_ratCast] using hcast

lemma catalanExp_centralBinom_cast (n : ℕ) :
    (n.centralBinom : ℝ) = ((2 * n).factorial : ℝ) /
      ((n.factorial : ℝ) * (n.factorial : ℝ)) := by
  have hle : n ≤ 2 * n := by omega
  have hchoose : (2 * n).choose n * (n.factorial * ((2 * n) - n).factorial) =
      (2 * n).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) hle
    rwa [mul_assoc] at h
  rw [show 2 * n - n = n by omega] at hchoose
  rw [Nat.centralBinom_eq_two_mul_choose]
  have hf : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  rw [eq_div_iff (mul_ne_zero hf.ne' hf.ne')]
  exact_mod_cast hchoose

lemma catalanExp_catalan_cast (n : ℕ) :
    (catalan n : ℝ) = (n.centralBinom : ℝ) / ((n : ℝ) + 1) := by
  have h := succ_mul_catalan_eq_centralBinom n
  rw [eq_div_iff (by positivity : (n : ℝ) + 1 ≠ 0), mul_comm]
  exact_mod_cast h

lemma catalanExp_stirling_model_identity (n : ℕ) (hn : 1 ≤ n) :
    ((Real.sqrt (2 * (2 * n : ℝ) * Real.pi) *
          ((2 * n : ℝ) / Real.exp 1) ^ (2 * n) /
        ((Real.sqrt (2 * (n : ℝ) * Real.pi) *
            ((n : ℝ) / Real.exp 1) ^ n) *
          (Real.sqrt (2 * (n : ℝ) * Real.pi) *
            ((n : ℝ) / Real.exp 1) ^ n)) /
        ((n : ℝ) + 1)) *
      ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)) =
        (n : ℝ) / ((n : ℝ) + 1) := by
  have hn0 : 0 < n := by omega
  have ha : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnn : (0 : ℝ) ≤ (n : ℝ) * Real.pi :=
    mul_nonneg ha.le Real.pi_pos.le
  have hsq2 : Real.sqrt (2 * (2 * n : ℝ) * Real.pi) =
      2 * Real.sqrt ((n : ℝ) * Real.pi) := by
    have hsqnn : (0 : ℝ) ≤ 2 * Real.sqrt ((n : ℝ) * Real.pi) := by positivity
    have heq : (2 : ℝ) * (2 * n : ℝ) * Real.pi =
        (2 * Real.sqrt ((n : ℝ) * Real.pi)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hnn]
      ring
    rw [heq, Real.sqrt_sq hsqnn]
  have hsq1sq : (Real.sqrt (2 * (n : ℝ) * Real.pi)) ^ 2 =
      2 * (n : ℝ) * Real.pi := Real.sq_sqrt (by positivity)
  have hS1S1 :
      (Real.sqrt (2 * (n : ℝ) * Real.pi) * ((n : ℝ) / Real.exp 1) ^ n) *
        (Real.sqrt (2 * (n : ℝ) * Real.pi) * ((n : ℝ) / Real.exp 1) ^ n) =
      (2 * (n : ℝ) * Real.pi) *
        (((n : ℝ) / Real.exp 1) ^ n * ((n : ℝ) / Real.exp 1) ^ n) := by
    calc
      _ = (Real.sqrt (2 * (n : ℝ) * Real.pi)) ^ 2 *
          (((n : ℝ) / Real.exp 1) ^ n * ((n : ℝ) / Real.exp 1) ^ n) := by ring
      _ = _ := by rw [hsq1sq]
  have hPu : ((2 * n : ℝ) / Real.exp 1) ^ n =
      (2 : ℝ) ^ n * ((n : ℝ) / Real.exp 1) ^ n := by
    rw [div_pow, mul_pow, mul_div_assoc, ← div_pow]
  have h4 : (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      show 2 * n = n + n by omega, pow_add]
  have hs3 : Real.sqrt (Real.pi * (n : ℝ)) =
      Real.sqrt ((n : ℝ) * Real.pi) := by rw [mul_comm]
  have hdouble : ((2 * n : ℝ) / Real.exp 1) ^ (2 * n) =
      ((2 * n : ℝ) / Real.exp 1) ^ n *
        ((2 * n : ℝ) / Real.exp 1) ^ n := by
    rw [show 2 * n = n + n by omega, pow_add]
  rw [hsq2, hdouble, hPu, hS1S1, h4, hs3]
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2aπ : (2 : ℝ) * n * Real.pi ≠ 0 := by positivity
  have hae : (n : ℝ) / Real.exp 1 ≠ 0 := (div_pos ha he).ne'
  have hp : ((n : ℝ) / Real.exp 1) ^ n ≠ 0 := pow_ne_zero _ hae
  have ha1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hQ : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hs2 : (Real.sqrt ((n : ℝ) * Real.pi)) ^ 2 =
      (n : ℝ) * Real.pi := Real.sq_sqrt hnn
  field_simp [h2aπ, hae, hp, ha1, hQ, he.ne']
  ring_nf
  rw [hs2]

theorem catalanExp_first_log_tendsto_zero :
    Filter.Tendsto (fun n : ℕ =>
      Real.log ((catalan n : ℝ) * ((n : ℝ) * Real.sqrt (Real.pi * n)) /
        (4 : ℝ) ^ n)) Filter.atTop (nhds 0) := by
  have h2top : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop_of_monotone
    · intro a b hab
      change 2 * a ≤ 2 * b
      omega
    · intro b
      exact ⟨b, by omega⟩
  have hFact := Stirling.factorial_isEquivalent_stirling
  have hFact2 := hFact.comp_tendsto h2top
  have eCB : Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => ((2 * n).factorial : ℝ) /
        ((n.factorial : ℝ) * (n.factorial : ℝ)))
      (fun n : ℕ => (Real.sqrt (2 * (2 * n : ℝ) * Real.pi) *
          ((2 * n : ℝ) / Real.exp 1) ^ (2 * n)) /
        ((Real.sqrt (2 * (n : ℝ) * Real.pi) * ((n : ℝ) / Real.exp 1) ^ n) *
          (Real.sqrt (2 * (n : ℝ) * Real.pi) * ((n : ℝ) / Real.exp 1) ^ n))) :=
    by
      convert hFact2.div (hFact.mul hFact) using 1 <;>
        ext n <;> simp [Function.comp_apply]
  have rNp1 : Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (n : ℝ) + 1) (fun n : ℕ => (n : ℝ) + 1) :=
    Asymptotics.IsEquivalent.refl
  have rR : Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)
      (fun n : ℕ => (n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n) :=
    Asymptotics.IsEquivalent.refl
  have eST : Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ =>
        ((Real.sqrt (2 * (2 * n : ℝ) * Real.pi) *
              ((2 * n : ℝ) / Real.exp 1) ^ (2 * n) /
            ((Real.sqrt (2 * (n : ℝ) * Real.pi) *
                ((n : ℝ) / Real.exp 1) ^ n) *
              (Real.sqrt (2 * (n : ℝ) * Real.pi) *
                ((n : ℝ) / Real.exp 1) ^ n)) /
            ((n : ℝ) + 1)) *
          ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)))
      (fun n : ℕ =>
        ((((2 * n).factorial : ℝ) /
              ((n.factorial : ℝ) * (n.factorial : ℝ)) /
            ((n : ℝ) + 1)) *
          ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n))) :=
    ((eCB.div rNp1).mul rR).symm
  have hmodel : Filter.EventuallyEq Filter.atTop
      (fun n : ℕ =>
        ((Real.sqrt (2 * (2 * n : ℝ) * Real.pi) *
              ((2 * n : ℝ) / Real.exp 1) ^ (2 * n) /
            ((Real.sqrt (2 * (n : ℝ) * Real.pi) *
                ((n : ℝ) / Real.exp 1) ^ n) *
              (Real.sqrt (2 * (n : ℝ) * Real.pi) *
                ((n : ℝ) / Real.exp 1) ^ n)) /
            ((n : ℝ) + 1)) *
          ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)))
      (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact catalanExp_stirling_model_identity n hn
  have hzero : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio : Filter.Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1))
      Filter.atTop (nhds 1) := by
    have h : Filter.Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds (1 - 0)) := tendsto_const_nhds.sub hzero
    rw [sub_zero] at h
    refine h.congr fun n => ?_
    field_simp
    ring
  have hStirlingModel : Filter.Tendsto
      (fun n : ℕ =>
        ((Real.sqrt (2 * (2 * n : ℝ) * Real.pi) *
              ((2 * n : ℝ) / Real.exp 1) ^ (2 * n) /
            ((Real.sqrt (2 * (n : ℝ) * Real.pi) *
                ((n : ℝ) / Real.exp 1) ^ n) *
              (Real.sqrt (2 * (n : ℝ) * Real.pi) *
                ((n : ℝ) / Real.exp 1) ^ n)) /
            ((n : ℝ) + 1)) *
          ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)))
      Filter.atTop (nhds 1) := Filter.Tendsto.congr' hmodel.symm hratio
  have hfactorialModel : Filter.Tendsto
      (fun n : ℕ =>
        ((((2 * n).factorial : ℝ) /
              ((n.factorial : ℝ) * (n.factorial : ℝ)) /
            ((n : ℝ) + 1)) *
          ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)))
      Filter.atTop (nhds 1) := eST.tendsto_nhds hStirlingModel
  have hCatalanModel : Filter.EventuallyEq Filter.atTop
      (fun n : ℕ =>
        ((((2 * n).factorial : ℝ) /
              ((n.factorial : ℝ) * (n.factorial : ℝ)) /
            ((n : ℝ) + 1)) *
          ((n : ℝ) * Real.sqrt (Real.pi * n) / (4 : ℝ) ^ n)))
      (fun n : ℕ =>
        (catalan n : ℝ) * ((n : ℝ) * Real.sqrt (Real.pi * n)) /
          (4 : ℝ) ^ n) := by
    filter_upwards with n
    rw [← catalanExp_centralBinom_cast n, ← catalanExp_catalan_cast n]
    ring
  have htarget : Filter.Tendsto (fun n : ℕ =>
      (catalan n : ℝ) * ((n : ℝ) * Real.sqrt (Real.pi * n)) /
        (4 : ℝ) ^ n) Filter.atTop (nhds 1) :=
    Filter.Tendsto.congr' hCatalanModel hfactorialModel
  simpa using htarget.log (by norm_num : (1 : ℝ) ≠ 0)

lemma catalanExp_catalan_pos (n : ℕ) : (0 : ℝ) < catalan n := by
  have h := succ_mul_catalan_eq_centralBinom n
  have hpos : 0 < (n + 1) * catalan n := by
    rw [h]
    exact Nat.centralBinom_pos n
  have hne : catalan n ≠ 0 := by
    intro hzero
    simp only [hzero, mul_zero, lt_self_iff_false] at hpos
  exact_mod_cast Nat.pos_of_ne_zero hne

lemma catalanExp_catalan_succ_ratio (n : ℕ) :
    (catalan (n + 1) : ℝ) / catalan n =
      2 * (2 * (n : ℝ) + 1) / ((n : ℝ) + 2) := by
  have hcentral := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n + 1),
    ← succ_mul_catalan_eq_centralBinom n] at hcentral
  have hcat : (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < n + 1)
    calc
      (n + 1) * ((n + 2) * catalan (n + 1)) =
          (n + 1) * ((n + 1 + 1) * catalan (n + 1)) := by
        rw [show n + 2 = n + 1 + 1 by omega]
      _ = 2 * (2 * n + 1) * ((n + 1) * catalan n) := hcentral
      _ = (n + 1) * (2 * (2 * n + 1) * catalan n) := by ring
  apply (div_eq_div_iff (catalanExp_catalan_pos n).ne' (by positivity)).2
  have hcat' : catalan (n + 1) * (n + 2) =
      2 * (2 * n + 1) * catalan n := by
    simpa [mul_comm] using hcat
  exact_mod_cast hcat'

lemma catalanExp_sum_bernoulli_aeval (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (n + 1),
        ((n + 1).choose k : ℝ) * Polynomial.aeval x (Polynomial.bernoulli k)) =
      (n + 1 : ℝ) * x ^ n := by
  have h := congrArg (Polynomial.aeval x) (Polynomial.sum_bernoulli n)
  simp only [map_sum, map_smul, Polynomial.aeval_monomial] at h
  simpa only [Algebra.smul_def, map_natCast, map_add, map_one] using h

lemma catalanExp_bernoulli_coeff (r : ℕ) (hr : 2 ≤ r) (α β : ℝ) :
    (∑ k ∈ Finset.range (r - 1),
        ((r - 1).choose k : ℝ) *
          (Polynomial.aeval α (Polynomial.bernoulli (k + 2)) -
            Polynomial.aeval β (Polynomial.bernoulli (k + 2))) /
          ((k + 1 : ℕ) * (k + 2 : ℕ))) =
      (α ^ r - β ^ r + β - α) / r := by
  let f : ℕ → ℝ := fun k => ((r + 1).choose k : ℝ) *
    (Polynomial.aeval α (Polynomial.bernoulli k) -
      Polynomial.aeval β (Polynomial.bernoulli k))
  have hfull : (∑ k ∈ Finset.range (r + 1), f k) =
      (r + 1 : ℝ) * (α ^ r - β ^ r) := by
    dsimp [f]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,
      catalanExp_sum_bernoulli_aeval, catalanExp_sum_bernoulli_aeval]
  have hsmall : (∑ k ∈ Finset.range 2, f k) = (r + 1 : ℝ) * (α - β) := by
    simp [f, Finset.sum_range_succ, Polynomial.aeval_def]
  have htail : (∑ k ∈ Finset.Ico 2 (r + 1), f k) =
      (r + 1 : ℝ) * (α ^ r - β ^ r + β - α) := by
    rw [Finset.sum_Ico_eq_sub f (by omega), hfull, hsmall]
    ring
  rw [Finset.sum_Ico_eq_sum_range f 2 (r + 1)] at htail
  rw [show r + 1 - 2 = r - 1 by omega] at htail
  have hshift : (∑ k ∈ Finset.range (r - 1), f (k + 2)) =
      (r + 1 : ℝ) * (α ^ r - β ^ r + β - α) := by
    simpa [add_comm] using htail
  have hchoose (k : ℕ) :
      ((r - 1).choose k : ℝ) / ((k + 1 : ℕ) * (k + 2 : ℕ)) =
        ((r + 1).choose (k + 2) : ℝ) / ((r : ℕ) * (r + 1 : ℕ)) := by
    have h₁ := Nat.add_one_mul_choose_eq (r - 1) k
    have h₂ := Nat.add_one_mul_choose_eq r (k + 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r)] at h₁
    rw [show k + 1 + 1 = k + 2 by omega] at h₂
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    norm_cast
    calc
      (r - 1).choose k * (r * (r + 1))
          = (r + 1) * (r * (r - 1).choose k) := by ring
      _ = (r + 1) * (r.choose (k + 1) * (k + 1)) := by rw [h₁]
      _ = ((r + 1) * r.choose (k + 1)) * (k + 1) := by ring
      _ = ((r + 1).choose (k + 2) * (k + 2)) * (k + 1) := by rw [h₂]
      _ = (r + 1).choose (k + 2) * ((k + 1) * (k + 2)) := by ring
  calc
    _ = (∑ k ∈ Finset.range (r - 1), f (k + 2)) /
        ((r : ℝ) * (r + 1 : ℝ)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      calc
        _ = (((r - 1).choose k : ℝ) /
            ((k + 1 : ℕ) * (k + 2 : ℕ))) *
              (Polynomial.aeval α (Polynomial.bernoulli (k + 2)) -
                Polynomial.aeval β (Polynomial.bernoulli (k + 2))) := by ring
        _ = (((r + 1).choose (k + 2) : ℝ) /
            ((r : ℕ) * (r + 1 : ℕ))) *
              (Polynomial.aeval α (Polynomial.bernoulli (k + 2)) -
                Polynomial.aeval β (Polynomial.bernoulli (k + 2))) := by rw [hchoose]
        _ = f (k + 2) / ((r : ℝ) * (r + 1 : ℝ)) := by
          dsimp [f]
          field_simp
          push_cast
          ring
    _ = _ := by
      rw [hshift]
      field_simp

end MetaMathlibExt
