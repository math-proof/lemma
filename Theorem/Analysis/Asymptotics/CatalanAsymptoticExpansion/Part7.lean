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
import Def.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part7
/-!
# Stirling-type asymptotic expansions of Catalan numbers

This file proves all-orders logarithmic asymptotic expansions of the Catalan
numbers by solving their first-difference equation with Bernoulli polynomials.
-/


namespace MetaMathlibExt

open scoped BigOperators

lemma catalanExp_logRemainder_isBigO (α β : ℝ) (M : ℕ) :
    catalanExpLogRemainder α β M =O[nhds 0] fun y : ℝ => y ^ (M + 2) := by
  unfold catalanExpLogRemainder
  have h1 : (fun y : ℝ => Real.log (1 + y) - catalanExpLogTaylor 1 (M + 1) y) =O[nhds 0]
      fun y : ℝ => y ^ (M + 2) := by
    apply (catalanExp_log_sub_taylor_isBigO 1 (M + 1)).congr_left
    intro y
    congr 2
    ring
  exact ((catalanExp_log_sub_taylor_isBigO α (M + 1)).sub
    (catalanExp_log_sub_taylor_isBigO β (M + 1))).add
      (h1.const_mul_left (β - α))

end MetaMathlibExt
