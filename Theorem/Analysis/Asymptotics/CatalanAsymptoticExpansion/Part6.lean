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
import Def.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part6
/-!
# Stirling-type asymptotic expansions of Catalan numbers

This file proves all-orders logarithmic asymptotic expansions of the Catalan
numbers by solving their first-difference equation with Bernoulli polynomials.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma catalanExp_shiftRemainder_isBigO (α β : ℝ) (M : ℕ) :
    catalanExpShiftRemainder α β M =O[nhds 0] fun y : ℝ => y ^ (M + 2) := by
  unfold catalanExpShiftRemainder
  have hsum : (∑ j ∈ Finset.range M, fun y : ℝ =>
      catalanExpBernoulliCoeff α β (j + 1) *
        (y ^ (j + 1) *
          ((1 + y) ^ (-((j + 1 : ℕ) : ℝ)) -
            catalanExpInvTaylor (j + 1) (M + 1 - j) y))) =O[nhds 0]
      fun y : ℝ => y ^ (M + 2) := by
    apply Asymptotics.IsBigO.sum
    intro j hj
    rw [Finset.mem_range] at hj
    have hmul := (Asymptotics.isBigO_refl (fun y : ℝ => y ^ (j + 1)) (nhds 0)).mul
      (catalanExp_rpow_sub_invTaylor_isBigO (j + 1) (M + 1 - j) (by omega))
    have hpow : (fun y : ℝ => y ^ (j + 1) * y ^ (M + 1 - j)) =
        fun y : ℝ => y ^ (M + 2) := by
      funext y
      rw [← pow_add, show j + 1 + (M + 1 - j) = M + 2 by omega]
    rw [hpow] at hmul
    exact hmul.const_mul_left (catalanExpBernoulliCoeff α β (j + 1))
  apply hsum.congr_left
  intro y
  exact Finset.sum_apply y (Finset.range M) _

lemma catalanExp_shift_sub_eq_remainder (α β : ℝ) (M : ℕ) (y : ℝ)
    (hy : 0 < 1 + y) :
    catalanExpBernoulliSum α β M (y / (1 + y)) -
        catalanExpBernoulliSum α β M y - catalanExpShiftTaylor α β M y =
      catalanExpShiftRemainder α β M y := by
  unfold catalanExpBernoulliSum catalanExpShiftTaylor catalanExpShiftRemainder
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hratio : (y / (1 + y)) ^ (j + 1) =
      y ^ (j + 1) * (1 + y) ^ (-((j + 1 : ℕ) : ℝ)) := by
    rw [div_pow, Real.rpow_neg (le_of_lt hy), Real.rpow_natCast]
    rfl
  rw [hratio, ← catalanExp_mul_invTaylor_sub_one M j hj y]
  ring

end MetaMathlibExt
