/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tan.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry16Tanseries
import Lemma.Real.Ramanujan.Part1Ch9Entry16Tanseries
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Smeval
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry16Tan

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9Entry16LogTerm (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * Real.log |2 * Real.sin x|

def chapter9SineFourierTwoTerm (x : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  Real.sin (2 * (k : ℝ) * x) / ((k : ℝ) ^ 2)

private def chap9Fcoeff (n : ℕ) : ℝ := (Nat.choose (2 * n) n : ℝ) / (2 : ℝ) ^ (2 * n)

private def chap9G (t : ℝ) : ℝ :=
  ∑' n : ℕ, chap9Fcoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

private def chap9F (t : ℝ) : ℝ :=
  ∑' n : ℕ, chap9Fcoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2

private def chap9D (θ : ℝ) : ℝ := Real.cos θ / Real.sinc θ

private def chap9Phi (θ : ℝ) : ℝ := chap9F (Real.sin θ)

private def chap9A (θ : ℝ) : ℝ := θ * Real.log (Real.sin θ)

private def chap9r (n : ℕ) : ℝ := 1 - 1 / (2 * ((n : ℝ) + 1))

private def chap9S (r x : ℝ) : ℝ :=
  ∑' j : ℕ, r ^ (j + 1) * chapter9SineFourierTwoTerm x j

private def chap9z (r x : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)
end
end Entry16Tan
end MathlibExt.Analysis.Ramanujan.Part1Ch9
