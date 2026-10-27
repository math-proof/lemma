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
import Theorem.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part7
/-!
# Stirling-type asymptotic expansions of Catalan numbers

This file proves all-orders logarithmic asymptotic expansions of the Catalan
numbers by solving their first-difference equation with Bernoulli polynomials.
-/


namespace MetaMathlibExt

open scoped BigOperators

noncomputable def catalanExpLocalResidual (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  catalanExpLogStep α β y -
    (catalanExpBernoulliSum α β M (y / (1 + y)) -
      catalanExpBernoulliSum α β M y)

end MetaMathlibExt
