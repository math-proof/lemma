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
public import Theorem.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part4

@[expose] public section

/-!
# Stirling-type asymptotic expansions of Catalan numbers

This file proves all-orders logarithmic asymptotic expansions of the Catalan
numbers by solving their first-difference equation with Bernoulli polynomials.
-/


namespace MetaMathlibExt

open scoped BigOperators

noncomputable def catalanExpBernoulliCoeff (α β : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k + 1) *
    (Polynomial.aeval α (Polynomial.bernoulli (k + 1)) -
      Polynomial.aeval β (Polynomial.bernoulli (k + 1))) /
    ((k : ℝ) * (k + 1 : ℕ))

noncomputable def catalanExpDiffCoeff (α β : ℝ) (r : ℕ) : ℝ :=
  (-1 : ℝ) ^ (r + 1) * (α ^ r - β ^ r + β - α) / r

noncomputable def catalanExpShiftInner (M j : ℕ) (y : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (M - j),
    (-1 : ℝ) ^ (q + 1) * ((j + q + 1).choose (q + 1) : ℝ) * y ^ (j + q + 2)

noncomputable def catalanExpShiftTaylor (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M,
    catalanExpBernoulliCoeff α β (j + 1) * catalanExpShiftInner M j y

noncomputable def catalanExpDiffTaylor (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, catalanExpDiffCoeff α β (j + 2) * y ^ (j + 2)

end MetaMathlibExt
