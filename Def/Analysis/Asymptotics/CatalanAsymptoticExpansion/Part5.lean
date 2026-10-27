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
import Theorem.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part4
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
