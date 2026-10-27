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
import Def.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part5
/-!
# Stirling-type asymptotic expansions of Catalan numbers

This file proves all-orders logarithmic asymptotic expansions of the Catalan
numbers by solving their first-difference equation with Bernoulli polynomials.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma catalanExp_logTaylor_combination (α β : ℝ) (M : ℕ) (y : ℝ) :
    catalanExpLogTaylor α (M + 1) y - catalanExpLogTaylor β (M + 1) y +
        (β - α) * catalanExpLogTaylor 1 (M + 1) y =
      catalanExpDiffTaylor α β M y := by
  induction M with
  | zero =>
      simp [catalanExpLogTaylor, catalanExpDiffTaylor]
      ring
  | succ M ih =>
      have hTaylor (a : ℝ) :
          catalanExpLogTaylor a (M + 2) y =
            catalanExpLogTaylor a (M + 1) y +
              (-1 : ℝ) ^ (M + 1) * a ^ (M + 2) / (M + 2 : ℕ) * y ^ (M + 2) := by
        unfold catalanExpLogTaylor
        rw [Finset.sum_range_succ]
      have hDiff : catalanExpDiffTaylor α β (M + 1) y =
          catalanExpDiffTaylor α β M y +
            catalanExpDiffCoeff α β (M + 2) * y ^ (M + 2) := by
        unfold catalanExpDiffTaylor
        rw [Finset.sum_range_succ]
      have hnew :
          (-1 : ℝ) ^ (M + 1) * α ^ (M + 2) / (M + 2 : ℕ) * y ^ (M + 2) -
              (-1 : ℝ) ^ (M + 1) * β ^ (M + 2) / (M + 2 : ℕ) * y ^ (M + 2) +
            (β - α) *
              ((-1 : ℝ) ^ (M + 1) * 1 ^ (M + 2) / (M + 2 : ℕ) * y ^ (M + 2)) =
            catalanExpDiffCoeff α β (M + 2) * y ^ (M + 2) := by
        simp only [one_pow, catalanExpDiffCoeff]
        rw [show (-1 : ℝ) ^ (M + 2 + 1) = (-1 : ℝ) ^ (M + 1) by
          rw [show M + 2 + 1 = (M + 1) + 2 by omega, pow_add]
          norm_num]
        field_simp
        ring
      change
        catalanExpLogTaylor α (M + 2) y - catalanExpLogTaylor β (M + 2) y +
            (β - α) * catalanExpLogTaylor 1 (M + 2) y =
          catalanExpDiffTaylor α β (M + 1) y
      rw [hTaylor α, hTaylor β, hTaylor 1, hDiff]
      linear_combination ih + hnew

lemma catalanExp_shiftInner_succ (M j : ℕ) (hj : j < M) (y : ℝ) :
    catalanExpShiftInner (M + 1) j y = catalanExpShiftInner M j y +
      (-1 : ℝ) ^ (M - j + 1) * ((M + 1).choose (M - j + 1) : ℝ) * y ^ (M + 2) := by
  unfold catalanExpShiftInner
  have hsub : M + 1 - j = (M - j) + 1 := by omega
  rw [hsub, Finset.sum_range_succ]
  rw [show j + (M - j) + 1 = M + 1 by omega,
    show j + (M - j) + 2 = M + 2 by omega]

lemma catalanExp_shiftTaylor_succ_raw (α β : ℝ) (M : ℕ) (y : ℝ) :
    catalanExpShiftTaylor α β (M + 1) y = catalanExpShiftTaylor α β M y +
      ∑ j ∈ Finset.range (M + 1),
        catalanExpBernoulliCoeff α β (j + 1) *
          ((-1 : ℝ) ^ (M - j + 1) * ((M + 1).choose (M - j + 1) : ℝ) *
            y ^ (M + 2)) := by
  have hlast : catalanExpShiftInner (M + 1) M y =
      (-1 : ℝ) ^ (M - M + 1) * ((M + 1).choose (M - M + 1) : ℝ) *
        y ^ (M + 2) := by
    simp [catalanExpShiftInner]
  have hsum :
      (∑ j ∈ Finset.range M,
          catalanExpBernoulliCoeff α β (j + 1) * catalanExpShiftInner (M + 1) j y) =
        (∑ j ∈ Finset.range M,
            catalanExpBernoulliCoeff α β (j + 1) * catalanExpShiftInner M j y) +
          ∑ j ∈ Finset.range M,
            catalanExpBernoulliCoeff α β (j + 1) *
              ((-1 : ℝ) ^ (M - j + 1) * ((M + 1).choose (M - j + 1) : ℝ) *
                y ^ (M + 2)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [catalanExp_shiftInner_succ M j hj]
    ring
  unfold catalanExpShiftTaylor
  rw [Finset.sum_range_succ, Finset.sum_range_succ, hlast, hsum]
  ring

lemma catalanExp_shift_diagonal (α β : ℝ) (M : ℕ) (y : ℝ) :
    (∑ j ∈ Finset.range (M + 1),
        catalanExpBernoulliCoeff α β (j + 1) *
          ((-1 : ℝ) ^ (M - j + 1) * ((M + 1).choose (M - j + 1) : ℝ) *
            y ^ (M + 2))) =
      catalanExpDiffCoeff α β (M + 2) * y ^ (M + 2) := by
  have hterms :
      (∑ j ∈ Finset.range (M + 1),
          catalanExpBernoulliCoeff α β (j + 1) *
            ((-1 : ℝ) ^ (M - j + 1) * ((M + 1).choose (M - j + 1) : ℝ) *
              y ^ (M + 2))) =
        ∑ j ∈ Finset.range (M + 1),
          (-1 : ℝ) ^ (M + 3) *
            (((M + 1).choose j : ℝ) *
              (Polynomial.aeval α (Polynomial.bernoulli (j + 2)) -
                Polynomial.aeval β (Polynomial.bernoulli (j + 2))) /
              ((j + 1 : ℕ) * (j + 2 : ℕ))) * y ^ (M + 2) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hjle : j ≤ M + 1 := Nat.le_of_lt hj
    have hsub : M - j + 1 = M + 1 - j := by omega
    rw [hsub, Nat.choose_symm hjle]
    unfold catalanExpBernoulliCoeff
    have hsign : (-1 : ℝ) ^ (j + 2) * (-1 : ℝ) ^ (M + 1 - j) =
        (-1 : ℝ) ^ (M + 3) := by
      rw [← pow_add, show j + 2 + (M + 1 - j) = M + 3 by omega]
    rw [show j + 1 + 1 = j + 2 by omega]
    push_cast
    calc
      _ = ((-1 : ℝ) ^ (j + 2) * (-1 : ℝ) ^ (M + 1 - j)) *
          (((M + 1).choose j : ℝ) *
            (Polynomial.aeval α (Polynomial.bernoulli (j + 2)) -
              Polynomial.aeval β (Polynomial.bernoulli (j + 2))) /
            ((j + 1 : ℝ) * (j + 2 : ℝ))) * y ^ (M + 2) := by ring
      _ = _ := by rw [hsign]
  rw [hterms]
  have hcoeff := catalanExp_bernoulli_coeff (M + 2) (by omega) α β
  have hcoeff' :
      (∑ j ∈ Finset.range (M + 1),
          ((M + 1).choose j : ℝ) *
            (Polynomial.aeval α (Polynomial.bernoulli (j + 2)) -
              Polynomial.aeval β (Polynomial.bernoulli (j + 2))) /
            ((j + 1 : ℕ) * (j + 2 : ℕ))) =
        (α ^ (M + 2) - β ^ (M + 2) + β - α) / (M + 2 : ℕ) := by
    simpa only [show M + 2 - 1 = M + 1 by omega] using hcoeff
  calc
    (∑ j ∈ Finset.range (M + 1),
        (-1 : ℝ) ^ (M + 3) *
          (((M + 1).choose j : ℝ) *
            (Polynomial.aeval α (Polynomial.bernoulli (j + 2)) -
              Polynomial.aeval β (Polynomial.bernoulli (j + 2))) /
            ((j + 1 : ℕ) * (j + 2 : ℕ))) * y ^ (M + 2)) =
      ((-1 : ℝ) ^ (M + 3) *
        ∑ j ∈ Finset.range (M + 1),
          ((M + 1).choose j : ℝ) *
            (Polynomial.aeval α (Polynomial.bernoulli (j + 2)) -
              Polynomial.aeval β (Polynomial.bernoulli (j + 2))) /
            ((j + 1 : ℕ) * (j + 2 : ℕ))) * y ^ (M + 2) := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by
      rw [hcoeff']
      unfold catalanExpDiffCoeff
      ring

lemma catalanExp_shiftTaylor_eq_diffTaylor (α β : ℝ) (M : ℕ) (y : ℝ) :
    catalanExpShiftTaylor α β M y = catalanExpDiffTaylor α β M y := by
  induction M with
  | zero => simp [catalanExpShiftTaylor, catalanExpDiffTaylor]
  | succ M ih =>
      rw [catalanExp_shiftTaylor_succ_raw, catalanExp_shift_diagonal, ih]
      unfold catalanExpDiffTaylor
      rw [Finset.sum_range_succ]

lemma catalanExp_mul_invTaylor_sub_one (M j : ℕ) (hj : j < M) (y : ℝ) :
    y ^ (j + 1) * (catalanExpInvTaylor (j + 1) (M + 1 - j) y - 1) =
      catalanExpShiftInner M j y := by
  have hsub : M + 1 - j = (M - j) + 1 := by omega
  unfold catalanExpInvTaylor catalanExpShiftInner
  rw [hsub, Finset.sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [add_sub_cancel_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [show j + 1 + (q + 1) - 1 = j + q + 1 by omega]
  calc
    _ = (-1 : ℝ) ^ (q + 1) * ((j + q + 1).choose (q + 1) : ℝ) *
        (y ^ (j + 1) * y ^ (q + 1)) := by ring
    _ = _ := by
      rw [← pow_add, show j + 1 + (q + 1) = j + q + 2 by omega]

end MetaMathlibExt
