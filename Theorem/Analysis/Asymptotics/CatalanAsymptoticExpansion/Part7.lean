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
public import Def.Analysis.Asymptotics.CatalanAsymptoticExpansion.Part7


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
