/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part4

@[expose] public section

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
