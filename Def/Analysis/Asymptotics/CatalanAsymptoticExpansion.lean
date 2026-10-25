/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Asymptotics/CatalanAsymptoticExpansion.lean -/

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
/-!
# Stirling-type asymptotic expansions of Catalan numbers

This file proves all-orders logarithmic asymptotic expansions of the Catalan
numbers by solving their first-difference equation with Bernoulli polynomials.
-/


namespace MetaMathlibExt

open scoped BigOperators

noncomputable def catalanExpBernoulliPolynomialEval (n : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (Polynomial.bernoulli n)

noncomputable def catalanExpEulerEvenQ (m : ℕ) : ℚ :=
  -(4 : ℚ) ^ (2 * m + 1) *
      (Polynomial.bernoulli (2 * m + 1)).eval (1 / 4) / (2 * m + 1 : ℕ)

noncomputable def catalanExpLogTaylor (a : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N,
    (-1 : ℝ) ^ i * a ^ (i + 1) / (i + 1 : ℕ) * y ^ (i + 1)

noncomputable def catalanExpInvTaylor (k N : ℕ) (y : ℝ) : ℝ :=
  ∑ l ∈ Finset.range N,
    (-1 : ℝ) ^ l * ((k + l - 1).choose l : ℝ) * y ^ l

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

noncomputable def catalanExpBernoulliSum (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, catalanExpBernoulliCoeff α β (j + 1) * y ^ (j + 1)

noncomputable def catalanExpShiftRemainder (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range M, catalanExpBernoulliCoeff α β (j + 1) *
    (y ^ (j + 1) *
      ((1 + y) ^ (-((j + 1 : ℕ) : ℝ)) -
        catalanExpInvTaylor (j + 1) (M + 1 - j) y))

noncomputable def catalanExpLogStep (α β : ℝ) (y : ℝ) : ℝ :=
  Real.log (1 + α * y) - Real.log (1 + β * y) +
    (β - α) * Real.log (1 + y)

noncomputable def catalanExpLogRemainder (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  (Real.log (1 + α * y) - catalanExpLogTaylor α (M + 1) y) -
    (Real.log (1 + β * y) - catalanExpLogTaylor β (M + 1) y) +
    (β - α) * (Real.log (1 + y) - catalanExpLogTaylor 1 (M + 1) y)

noncomputable def catalanExpLocalResidual (α β : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  catalanExpLogStep α β y -
    (catalanExpBernoulliSum α β M (y / (1 + y)) -
      catalanExpBernoulliSum α β M y)

end MetaMathlibExt
