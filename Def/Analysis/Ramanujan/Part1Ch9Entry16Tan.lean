module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Def.Analysis.Ramanujan.Part1Ch9Entry16Tanseries
public import Theorem.Real.Ramanujan.Part1Ch9Entry16Tanseries
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Polynomial.Smeval
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.RingTheory.Binomial
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry16Tan.lean -/
/-
Author: @akiezun, Avocado
-/
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/
section

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

def chap9Fcoeff (n : ℕ) : ℝ := (Nat.choose (2 * n) n : ℝ) / (2 : ℝ) ^ (2 * n)

def chap9G (t : ℝ) : ℝ :=
  ∑' n : ℕ, chap9Fcoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

def chap9F (t : ℝ) : ℝ :=
  ∑' n : ℕ, chap9Fcoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2

def chap9D (θ : ℝ) : ℝ := Real.cos θ / Real.sinc θ

def chap9Phi (θ : ℝ) : ℝ := chap9F (Real.sin θ)

def chap9A (θ : ℝ) : ℝ := θ * Real.log (Real.sin θ)

def chap9r (n : ℕ) : ℝ := 1 - 1 / (2 * ((n : ℝ) + 1))

def chap9S (r x : ℝ) : ℝ :=
  ∑' j : ℕ, r ^ (j + 1) * chapter9SineFourierTwoTerm x j

def chap9z (r x : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)

end
end Entry16Tan
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
