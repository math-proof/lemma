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
public import Theorem.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part5


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Stirling-type asymptotic expansions of Catalan numbers

This file proves all-orders logarithmic asymptotic expansions of the Catalan
numbers by solving their first-difference equation with Bernoulli polynomials.
-/
namespace MetaMathlibExt

open scoped BigOperators

noncomputable def catalanExpBernoulliSum (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, catalanExpBernoulliCoeff α β (j + 1) * y ^ (j + 1)

noncomputable def catalanExpShiftRemainder (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, catalanExpBernoulliCoeff α β (j + 1) *
    (y ^ (j + 1) *
      ((1 + y) ^ (-((j + 1 : ℕ) : ℝ)) -
        catalanExpInvTaylor (j + 1) (M + 1 - j) y))

end MetaMathlibExt
