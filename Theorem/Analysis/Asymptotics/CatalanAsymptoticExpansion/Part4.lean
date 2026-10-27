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
import Def.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part4
/-!
# Stirling-type asymptotic expansions of Catalan numbers

This file proves all-orders logarithmic asymptotic expansions of the Catalan
numbers by solving their first-difference equation with Bernoulli polynomials.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma catalanExp_rpow_sub_invTaylor_isBigO (k N : ℕ) (hk : 1 ≤ k) :
    (fun y : ℝ => (1 + y) ^ (-(k : ℝ)) - catalanExpInvTaylor k N y) =O[nhds 0]
      fun y : ℝ => y ^ N := by
  have h := (Real.one_add_rpow_hasFPowerSeriesAt_zero (a := -(k : ℝ))).isBigO_sub_partialSum_pow N
  rw [show (binomialSeries ℝ (-(k : ℝ))).partialSum N =
      catalanExpInvTaylor k N by
        funext y
        exact catalanExp_binomial_partialSum k N hk y] at h
  apply Asymptotics.IsBigO.of_norm_right
  simpa only [zero_add, Real.norm_eq_abs, abs_pow] using h

end MetaMathlibExt
